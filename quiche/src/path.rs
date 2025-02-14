// Copyright (C) 2022, Cloudflare, Inc.
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
//     * Redistributions of source code must retain the above copyright notice,
//       this list of conditions and the following disclaimer.
//
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
// IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
// THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
// PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
// CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use std::cmp;
use std::time;

use std::collections::BTreeMap;
use std::collections::VecDeque;
use std::net::SocketAddr;

use smallvec::SmallVec;

use slab::Slab;

use crate::recovery::RecoveryConfig;
use crate::recovery::RttStats;
use crate::CIDSeq;
use crate::Error;
use crate::InternalPathId;
use crate::PathId;
use crate::PathIdWithCidSeq;
use crate::Result;

use crate::pmtud;
use crate::recovery;
use crate::recovery::HandshakeStatus;

/// The different states of the path validation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum NetworkPathValidationState {
    /// The network path failed its validation.
    Failed,

    /// The network path exists, but no path validation has been performed.
    Unknown,

    /// The network path is under validation.
    Validating,

    /// The remote address has been validated, but not the network path MTU.
    ValidatingMTU,

    /// The network path has been validated.
    Validated,
}

impl NetworkPathValidationState {
    #[cfg(feature = "ffi")]
    pub fn to_c(self) -> libc::ssize_t {
        match self {
            NetworkPathValidationState::Failed => -1,
            NetworkPathValidationState::Unknown => 0,
            NetworkPathValidationState::Validating => 1,
            NetworkPathValidationState::ValidatingMTU => 2,
            NetworkPathValidationState::Validated => 3,
        }
    }
}

/// The different usage states of the QUIC path.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathState {
    /// The path only sends probing packets.
    Unused,
    /// The path can send non-probing packets.
    Active,
    /// The path is under closing process.
    Closing(u64),
    /// The path is now closed.
    Closed(u64),
}

/// The different requests that can be assigned to a path.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathRequest {
    /// The path should not send non-probing packets.
    Unused,
    /// The path can send any packets.
    Active,
    /// The path should be abandonned, with the provided error code.
    Abandon(u64),
}

impl PathRequest {
    fn requested_state(self) -> PathState {
        match self {
            PathRequest::Unused => PathState::Unused,
            PathRequest::Active => PathState::Active,
            PathRequest::Abandon(e) => PathState::Closing(e),
        }
    }
}

/// The status of a path, advertised through the PATH_STATUS frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathStatus {
    /// The host should stop sending non-probing packets on the path.
    Backup,

    /// The host should consider this path to send non-probing packets.
    Available,
}

impl From<PathStatus> for bool {
    fn from(s: PathStatus) -> Self {
        matches!(s, PathStatus::Available)
    }
}

impl From<bool> for PathStatus {
    fn from(v: bool) -> Self {
        match v {
            false => PathStatus::Backup,
            true => PathStatus::Available,
        }
    }
}

/// A path-specific event.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathEvent {
    /// A new network path (local address, peer address) has been seen on a
    /// received packet. Note that this event is only triggered for servers, as
    /// the client is responsible from initiating new paths. It is the
    /// application responsibility to define whether this path should be probed
    /// and used.
    New(SocketAddr, SocketAddr),

    /// The related network path between local `SocketAddr` and peer
    /// `SocketAddr` has been validated.
    Validated(SocketAddr, SocketAddr),

    /// The related network path between local `SocketAddr` and peer
    /// `SocketAddr` failed to be validated. This network path will not be used
    /// anymore, unless the application requests probing this path again.
    FailedValidation(SocketAddr, SocketAddr),

    /// The path has been closed and is now unusable on this connection.
    /// This event indicates the last network path that has been used, i.e.,
    /// between local `SocketAddr` and peer `SocketAddr`. An error code is
    /// provided.
    Closed(SocketAddr, SocketAddr, u64),

    /// The stack observes that the Source Connection ID with the given sequence
    /// number, initially used by the peer over the first pair of `SocketAddr`s,
    /// is now reused over the second pair of `SocketAddr`s.
    ReusedSourceConnectionId(
        CIDSeq,
        (SocketAddr, SocketAddr),
        (SocketAddr, SocketAddr),
    ),

    /// The connection observed that the peer migrated over the network path
    /// denoted by the pair of `SocketAddr`, i.e., non-probing packets have been
    /// received on this network path. This is a server side only event.
    ///
    /// Note that this event is only raised if the path has been validated.
    PeerMigrated(SocketAddr, SocketAddr),

    /// The peer advertised the following path status for the mentioned 4-tuple.
    /// TODO: Remove the addresses.
    PeerPathStatus((SocketAddr, SocketAddr), PathStatus),
}

/// Network path identifier, internally used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NetworkPathId(pub usize);

/// A network path on which QUIC packets can be sent.
pub struct NetworkPath {
    /// The local address.
    local_addr: SocketAddr,

    /// The remote address.
    peer_addr: SocketAddr,

    /// Source CID sequence number used over a given network path.
    pub active_scid_seqs: Slab<PathIdWithCidSeq>,

    /// Destination CID sequence number used over a given network path.
    pub active_dcid_seqs: Slab<PathIdWithCidSeq>,

    /// The current validation state of the path.
    validation_state: NetworkPathValidationState,

    /// RTT state of the network path.
    pub rtt_stats: recovery::RttStats,

    /// Path MTU discovery state.
    pub pmtud: pmtud::Pmtud,

    /// Pending challenge data with the Path ID on which they were sent, the
    /// size of the packet containing them and when they were sent.
    in_flight_challenges: VecDeque<([u8; 8], PathId, usize, time::Instant)>,

    /// The maximum challenge size that got acknowledged.
    max_challenge_size: usize,

    /// Number of consecutive (spaced by at least 1 RTT) probing packets lost.
    probing_lost: usize,

    /// Last instant when a probing packet got lost.
    last_probe_lost_time: Option<time::Instant>,

    /// Received challenge data.
    received_challenges: VecDeque<[u8; 8]>,

    /// Max length of received challenges queue.
    received_challenges_max_len: usize,

    /// Number of packets sent on this path.
    pub sent_count: usize,

    /// Number of packets received on this path.
    pub recv_count: usize,

    /// Total number of packets sent with data retransmitted from this path.
    pub _retrans_count: usize,

    /// Number of DATAGRAM frames sent on this path.
    pub _dgram_sent_count: usize,

    /// Number of DATAGRAM frames received on this path.
    pub _dgram_recv_count: usize,

    /// Total number of sent bytes over this path.
    pub sent_bytes: u64,

    /// Total number of bytes received over this path.
    pub recv_bytes: u64,

    /// Total number of bytes retransmitted from this path.
    /// This counts only STREAM and CRYPTO data.
    pub _stream_retrans_bytes: u64,

    /// Total number of bytes the server can send before the peer's address
    /// is verified.
    pub max_send_bytes: usize,

    /// Whether the peer's address has been verified.
    pub verified_peer_address: bool,

    /// Whether the peer has verified our address.
    pub peer_verified_local_address: bool,

    /// Does it requires sending PATH_CHALLENGE?
    challenge_requested: bool,

    /// Whether the failure of this path was notified.
    failure_notified: bool,

    /// Whether one connection's path tries to migrate to this network path, but
    /// it still needs to be validated.
    migrating: bool,
}

impl NetworkPath {
    /// Create a new NetworkPath instance with the provided addresses, the
    /// remaining of the fields being set to their default value.
    pub fn new(
        local_addr: SocketAddr, peer_addr: SocketAddr,
        path_challenge_recv_max_queue_len: usize, pmtud_init: usize,
        is_initial: bool, recovery_config: &RecoveryConfig,
    ) -> Self {
        // TODO: limit the number of entries in the slabs.
        let mut active_scid_seqs = Slab::with_capacity(1); // most network paths serve a single QUIC path
        let mut active_dcid_seqs = Slab::with_capacity(1); // most network paths serve a single QUIC path
        let validation_state = if is_initial {
            active_scid_seqs.insert(PathIdWithCidSeq(0, 0));
            active_dcid_seqs.insert(PathIdWithCidSeq(0, 0));
            NetworkPathValidationState::Validated
        } else {
            NetworkPathValidationState::Unknown
        };

        Self {
            local_addr,
            peer_addr,
            active_scid_seqs,
            active_dcid_seqs,
            validation_state,
            rtt_stats: RttStats::new(recovery_config.max_ack_delay),
            pmtud: pmtud::Pmtud::new(pmtud_init),
            in_flight_challenges: VecDeque::new(),
            max_challenge_size: 0,
            probing_lost: 0,
            last_probe_lost_time: None,
            received_challenges: VecDeque::with_capacity(
                path_challenge_recv_max_queue_len,
            ),
            received_challenges_max_len: path_challenge_recv_max_queue_len,
            sent_count: 0,
            recv_count: 0,
            _retrans_count: 0,
            _dgram_sent_count: 0,
            _dgram_recv_count: 0,
            sent_bytes: 0,
            recv_bytes: 0,
            _stream_retrans_bytes: 0,
            max_send_bytes: 0,
            verified_peer_address: false,
            peer_verified_local_address: false,
            challenge_requested: false,
            failure_notified: false,
            migrating: false,
        }
    }

    /// Returns the local address on which this network path operates.
    #[inline]
    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// Returns the peer address on which this network path operates.
    #[inline]
    pub fn peer_addr(&self) -> SocketAddr {
        self.peer_addr
    }

    /// Returns whether the network path is working (i.e., not failed).
    #[inline]
    pub fn working(&self) -> bool {
        self.validation_state > NetworkPathValidationState::Failed
    }

    /// Returns whether the network path is usable for the provided PathId.
    #[inline]
    fn active_for(&self, path_id: PathId) -> bool {
        self.working() &&
            self.active_dcid_seqs.iter().any(|(_, pc)| path_id == pc.0)
    }

    /// Returns whether the network path can be used to send non-probing
    /// packets for the provided PathId.
    #[inline]
    pub fn usable_for(&self, path_id: PathId) -> bool {
        self.validation_state == NetworkPathValidationState::Validated &&
            self.active_dcid_seqs.iter().any(|(_, pc)| path_id == pc.0)
    }

    /// Returns the Path IDs that can be associated to that network path.
    /// Note that this does not check whether the network path is the active one
    /// for the related Path ID.
    #[inline]
    pub fn path_ids(&self) -> impl ExactSizeIterator<Item = &PathId> {
        self.active_dcid_seqs.iter().map(|(_, pc)| &pc.0)
    }

    /// Returns whether the network path is unused.
    #[inline]
    fn unused(&self) -> bool {
        self.active_dcid_seqs.is_empty()
    }

    /// Returns whether the path requires sending a probing packet.
    #[inline]
    pub fn probing_required(&self) -> bool {
        !self.received_challenges.is_empty() || self.validation_requested()
    }

    /// Promotes the network path to the provided validation state only if the
    /// new state is greater than the current one.
    fn promote_to(&mut self, state: NetworkPathValidationState) {
        if self.validation_state < state {
            self.validation_state = state;
        }
    }

    /// Returns whether the network path is validated.
    #[inline]
    pub fn validated(&self) -> bool {
        self.validation_state == NetworkPathValidationState::Validated
    }

    /// Returns whether this network path failed its validation.
    #[inline]
    fn validation_failed(&self) -> bool {
        self.validation_state == NetworkPathValidationState::Failed
    }

    // Returns whether this network path is under path validation process.
    #[inline]
    pub fn under_validation(&self) -> bool {
        matches!(
            self.validation_state,
            NetworkPathValidationState::Validating |
                NetworkPathValidationState::ValidatingMTU
        )
    }

    /// Requests network path validation.
    #[inline]
    pub fn request_validation(&mut self) {
        self.challenge_requested = true;
    }

    /// Returns whether a validation is requested.
    #[inline]
    pub fn validation_requested(&self) -> bool {
        self.challenge_requested
    }

    pub fn should_send_pmtu_probe(
        &mut self, hs_confirmed: bool, hs_done: bool, out_len: usize,
        is_closing: bool, frames_empty: bool, cwnd_available: usize,
    ) -> bool {
        (hs_confirmed && hs_done) &&
            self.pmtud.get_probe_size() > self.pmtud.get_current() &&
            cwnd_available > self.pmtud.get_probe_size() &&
            out_len >= self.pmtud.get_probe_size() &&
            self.pmtud.get_probe_status() &&
            !is_closing &&
            frames_empty
    }

    pub fn on_challenge_sent(&mut self) {
        self.promote_to(NetworkPathValidationState::Validating);
        self.challenge_requested = false;
    }

    /// Handles the sending of PATH_CHALLENGE.
    pub fn add_challenge_sent(
        &mut self, data: [u8; 8], path_id: PathId, pkt_size: usize,
        sent_time: time::Instant,
    ) {
        self.on_challenge_sent();
        self.in_flight_challenges
            .push_back((data, path_id, pkt_size, sent_time));
    }

    pub fn on_challenge_received(&mut self, data: [u8; 8]) {
        // Discard challenges that would cause us to queue more than we want.
        if self.received_challenges.len() == self.received_challenges_max_len {
            return;
        }

        self.received_challenges.push_back(data);
        self.peer_verified_local_address = true;
    }

    pub fn has_pending_challenge(&self, data: [u8; 8]) -> bool {
        self.in_flight_challenges.iter().any(|(d, ..)| *d == data)
    }

    /// Returns whether the network path is now validated.
    pub fn on_response_received(&mut self, data: [u8; 8]) -> Option<PathId> {
        self.verified_peer_address = true;
        self.probing_lost = 0;

        let mut challenge_size = 0;
        let mut validated_on_path_id = None;
        self.in_flight_challenges.retain(|(d, path_id, s, _)| {
            if *d == data {
                challenge_size = *s;
                validated_on_path_id = Some(*path_id);
                false
            } else {
                true
            }
        });

        // The 4-tuple is reachable, but we didn't check Path MTU yet.
        self.promote_to(NetworkPathValidationState::ValidatingMTU);

        self.max_challenge_size =
            std::cmp::max(self.max_challenge_size, challenge_size);

        if self.validation_state == NetworkPathValidationState::ValidatingMTU {
            if self.max_challenge_size >= crate::MIN_CLIENT_INITIAL_LEN {
                // Path MTU is sufficient for QUIC traffic.
                self.promote_to(NetworkPathValidationState::Validated);
                return validated_on_path_id;
            }

            // If the MTU was not validated, probe again.
            self.request_validation();
        }

        None
    }

    fn on_failed_validation(&mut self) {
        self.validation_state = NetworkPathValidationState::Failed;
    }

    #[inline]
    pub fn pop_received_challenge(&mut self) -> Option<[u8; 8]> {
        self.received_challenges.pop_front()
    }

    pub fn on_loss_detection_timeout(
        &mut self, now: time::Instant, is_server: bool, rtt: time::Duration,
    ) {
        let mut lost_probe_time = None;
        self.in_flight_challenges.retain(|(_, _, _, sent_time)| {
            if *sent_time <= now {
                if lost_probe_time.is_none() {
                    lost_probe_time = Some(*sent_time);
                }
                false
            } else {
                true
            }
        });

        // If we lost probing packets, check if the path failed
        // validation.
        if let Some(lost_probe_time) = lost_probe_time {
            self.last_probe_lost_time = match self.last_probe_lost_time {
                Some(last) => {
                    // Count a loss if at least 1-RTT happened.
                    if lost_probe_time - last >= rtt {
                        self.probing_lost += 1;
                        Some(lost_probe_time)
                    } else {
                        Some(last)
                    }
                },
                None => {
                    self.probing_lost += 1;
                    Some(lost_probe_time)
                },
            };
            // As a server, if requesting a challenge is not
            // possible due to the amplification attack, declare the
            // validation as failed.
            if self.probing_lost >= crate::MAX_PROBING_TIMEOUTS ||
                (is_server && self.max_send_bytes < crate::MIN_PROBING_SIZE)
            {
                self.on_failed_validation();
            } else {
                self.request_validation();
            }
        }
    }

    pub fn dcid_seq_for_path_id(&self, path_id: PathId) -> Option<CIDSeq> {
        self.active_dcid_seqs
            .iter()
            .find_map(|(_, pc)| (pc.0 == path_id).then_some(pc.1))
    }

    pub fn scid_seq_for_path_id(&self, path_id: PathId) -> Option<CIDSeq> {
        self.active_scid_seqs
            .iter()
            .find_map(|(_, pc)| (pc.0 == path_id).then_some(pc.1))
    }

    pub fn rtt(&self) -> time::Duration {
        self.rtt_stats.rtt()
    }

    pub fn min_rtt(&self) -> Option<time::Duration> {
        self.rtt_stats.min_rtt()
    }

    pub fn rttvar(&self) -> time::Duration {
        self.rtt_stats.rttvar()
    }

    pub fn pto(&self) -> time::Duration {
        self.rtt_stats.pto()
    }

    pub fn rtt_update_count(&self) -> usize {
        self.rtt_stats.rtt_update_count()
    }
}

/// A QUIC path having its own packet space.
pub struct Path {
    /// The explicit path ID in multipath.
    path_id: PathId,

    /// The current NetworkPath identifier being used by this path.
    network_path_id: NetworkPathId,

    /// The usage state of this path.
    state: PathState,

    /// Loss recovery and congestion control state.
    pub recovery: recovery::Recovery,

    /// Number of packets sent on this path.
    pub sent_count: usize,

    /// Number of packets received on this path.
    pub recv_count: usize,

    /// Total number of packets sent with data retransmitted from this path.
    pub retrans_count: usize,

    /// Number of DATAGRAM frames sent on this path.
    pub dgram_sent_count: usize,

    /// Number of DATAGRAM frames received on this path.
    pub dgram_recv_count: usize,

    /// Total number of sent bytes over this path.
    pub sent_bytes: u64,

    /// Total number of bytes received over this path.
    pub recv_bytes: u64,

    /// Total number of bytes retransmitted from this path.
    /// This counts only STREAM and CRYPTO data.
    pub stream_retrans_bytes: u64,

    /// The timeout of closing the path.
    closing_timer: Option<std::time::Instant>,
    /// Whether the peer abandoned this path.
    peer_abandoned: bool,

    /// The scheduling status of this path.
    status: PathStatus,

    /// Whether the path closure has been notified to the application.
    closure_notified: bool,

    /// Whether or not we should force eliciting of an ACK (e.g. via PING frame)
    pub needs_ack_eliciting: bool,

    /// The expected sequence number of the PATH_STATUS to be received.
    expected_path_status_seq_num: u64,
}

impl Path {
    /// Create a new Path instance with the provided addresses, the remaining of
    /// the fields being set to their default value.
    pub fn new(
        path_id: PathId, network_path_id: NetworkPathId,
        recovery_config: &recovery::RecoveryConfig,
    ) -> Self {
        Self {
            path_id,
            network_path_id,
            state: PathState::Unused,
            recovery: recovery::Recovery::new_with_config(recovery_config),
            sent_count: 0,
            recv_count: 0,
            retrans_count: 0,
            dgram_sent_count: 0,
            dgram_recv_count: 0,
            sent_bytes: 0,
            recv_bytes: 0,
            stream_retrans_bytes: 0,
            closing_timer: None,
            peer_abandoned: false,
            status: PathStatus::Available,
            closure_notified: false,
            needs_ack_eliciting: false,
            expected_path_status_seq_num: 0,
        }
    }

    /// Returns whether the path is active on the provided network path.
    #[inline]
    pub fn active(
        &self, network_path_id: NetworkPathId, network_path: &NetworkPath,
    ) -> bool {
        self.state == PathState::Active &&
            self.network_path_id == network_path_id &&
            network_path.active_for(self.path_id)
    }

    /// Returns the path ID of the QUIC path.
    #[inline]
    pub fn path_id(&self) -> PathId {
        self.path_id
    }

    /// Returns whether this path is under closing process.
    #[inline]
    pub fn is_closing(&self) -> bool {
        matches!(self.state, PathState::Closing(_))
    }

    /// Returns whether this path is closed.
    #[inline]
    fn closed(&self) -> bool {
        matches!(self.state, PathState::Closed(_))
    }

    pub fn on_abandon_received(&mut self) {
        self.peer_abandoned = true;
    }

    pub fn on_closing_timeout(&mut self) {
        self.closing_timer = None;
    }

    pub fn closing_error_code(&self) -> Result<u64> {
        match &self.state {
            PathState::Closing(e) | PathState::Closed(e) => Ok(*e),
            _ => Err(Error::InvalidState),
        }
    }

    #[inline]
    fn valid_state_transition(&self, new_state: &PathState) -> bool {
        match (&self.state, new_state) {
            // In Unused or Active, we can transition to any state.
            (PathState::Unused, _) => true,
            (PathState::Active, _) => true,
            // In Closing, we can only transition to Closing or Closed.
            (PathState::Closing(..), PathState::Closing(..)) => true,
            (PathState::Closing(..), PathState::Closed(..)) => true,
            // In Close, we can only transition to itself.
            (PathState::Closed(..), PathState::Closed(..)) => true,
            // Any other transition is invalid.
            (..) => false,
        }
    }

    /// Sets the state of a path, returning an error if the transition is not
    /// valid.
    fn set_state(&mut self, state: PathState) -> Result<()> {
        if !self.valid_state_transition(&state) {
            return Err(Error::InvalidState);
        }

        self.state = state;
        Ok(())
    }

    /// Returns the time at which a timeout will occur on the path.
    #[inline]
    pub fn path_timer(&self) -> Option<time::Instant> {
        [self.closing_timer, self.recovery.loss_detection_timer()]
            .iter()
            .filter_map(|&t| t)
            .min()
    }

    #[inline]
    pub fn closing_timer(&self) -> Option<time::Instant> {
        self.closing_timer
    }

    pub fn on_loss_detection_timeout(
        &mut self, handshake_status: HandshakeStatus, now: time::Instant,
        reinject_all_on_pto: bool, rtt_stats: &RttStats, trace_id: &str,
    ) -> (usize, usize, SmallVec<[(NetworkPathId, time::Duration); 1]>) {
        let (lost_packets, lost_bytes, network_path_ids) =
            self.recovery.on_loss_detection_timeout(
                handshake_status,
                now,
                reinject_all_on_pto,
                rtt_stats,
                trace_id,
            );

        (lost_packets, lost_bytes, network_path_ids)
    }

    #[inline]
    pub fn is_backup(&self) -> bool {
        matches!(self.status, PathStatus::Backup)
    }

    #[inline]
    /// Whether this path is potentially lost (i.e., non-zero PTO count).
    pub fn potentially_lost(&self) -> bool {
        self.recovery.pto_count() > 0
    }

    #[inline]
    /// Returns the network path ID in use by the QUIC path.
    pub fn network_path_id(&self) -> NetworkPathId {
        self.network_path_id
    }

    pub fn stats(&self, network_path: &NetworkPath) -> PathStats {
        PathStats {
            path_id: self.path_id,
            local_addr: network_path.local_addr,
            peer_addr: network_path.peer_addr,
            validation_state: network_path.validation_state,
            state: self.state.clone(),
            active: self.active(self.network_path_id, network_path),
            recv: self.recv_count,
            sent: self.sent_count,
            lost: self.recovery.lost_count(),
            lost_spurious: self.recovery.lost_spurious_count(),
            retrans: self.retrans_count,
            dgram_recv: self.dgram_recv_count,
            dgram_sent: self.dgram_sent_count,
            rtt: network_path.rtt(),
            min_rtt: network_path.min_rtt(),
            rttvar: network_path.rttvar(),
            rtt_update: network_path.rtt_update_count(),
            cwnd: self.recovery.cwnd(),
            sent_bytes: self.sent_bytes,
            recv_bytes: self.recv_bytes,
            lost_bytes: self.recovery.bytes_lost,
            stream_retrans_bytes: self.stream_retrans_bytes,
            pmtu: self.recovery.max_datagram_size(),
            delivery_rate: self.recovery.delivery_rate(),
            pto_count: self.recovery.pto_count(),
        }
    }
}

/// An iterator over SocketAddr.
#[derive(Default, Debug)]
pub struct SocketAddrIter {
    pub(crate) sockaddrs_path_id: SmallVec<[(SocketAddr, PathId); 8]>,
    pub(crate) index: usize,
}

impl Iterator for SocketAddrIter {
    type Item = (SocketAddr, PathId);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let v = self.sockaddrs_path_id.get(self.index)?;
        self.index += 1;
        Some(*v)
    }
}

impl ExactSizeIterator for SocketAddrIter {
    #[inline]
    fn len(&self) -> usize {
        self.sockaddrs_path_id.len() - self.index
    }
}

type PmtudUpdate = (Option<u16>, u16, Option<bool>);

/// All path-related information.
pub struct PathMap {
    /// The network paths of the connection. Each of them has an internal
    /// identifier that is used by `addrs_to_paths` and `ConnectionEntry`.
    network_paths: Slab<NetworkPath>,

    /// The QUIC paths of the connection. Each of them has an internal
    /// identifier that is used by `addrs_to_paths` and `ConnectionEntry`.
    paths: Slab<Path>,

    /// The maximum number of concurrent network paths allowed.
    max_concurrent_network_paths: usize,

    /// The maximum number of concurrent QUIC paths allowed.
    max_concurrent_paths: usize,

    /// The mapping from the (local `SocketAddr`, peer `SocketAddr`) to the
    /// `NetworkPath` structure identifier.
    addrs_to_paths: BTreeMap<(SocketAddr, SocketAddr), NetworkPathId>,

    /// Path-specific events to be notified to the application.
    events: VecDeque<(PathId, PathEvent)>,

    /// Whether this manager serves a connection as a server.
    is_server: bool,

    /// Whether the multipath extensions are enabled.
    multipath: bool,

    /// Internal path identifiers requiring sending PATH_ABANDON frames.
    path_abandon: VecDeque<InternalPathId>,

    /// Whether a connection-wide PATH_STATUS frame should be sent.
    /// Send a PATH_AVAILABLE is true, otherwise PATH_BACKUP.
    path_status_to_advertise: VecDeque<(PathId, u64, bool)>,
    /// The sequence number for the next PATH_STATUS.
    next_path_status_seq_num: u64,
}

impl PathMap {
    /// Creates a new `PathMap` with the initial provided `path` and a
    /// capacity limit.
    pub fn new(
        mut initial_network_path: NetworkPath, mut initial_path: Path,
        max_concurrent_network_paths: usize, max_concurrent_paths: usize,
        is_server: bool, enable_pmtud: bool, max_send_udp_payload_size: usize,
    ) -> Self {
        let mut network_paths = Slab::with_capacity(1); // most connections only have one network path
        let mut paths = Slab::with_capacity(1); // most connections only have one path
        let mut addrs_to_paths = BTreeMap::new();

        let local_addr = initial_network_path.local_addr;
        let peer_addr = initial_network_path.peer_addr;

        // As it is the first path, it is active by default.
        initial_path.state = PathState::Active;

        // Enable path MTU Discovery and start probing with the largest datagram
        // size.
        if enable_pmtud {
            initial_network_path.pmtud.should_probe(enable_pmtud);
            initial_network_path
                .pmtud
                .set_probe_size(max_send_udp_payload_size);
            initial_network_path.pmtud.enable(enable_pmtud);
        }

        let active_network_path_id = network_paths.insert(initial_network_path);
        initial_path.network_path_id = NetworkPathId(active_network_path_id);
        paths.insert(initial_path);
        addrs_to_paths.insert(
            (local_addr, peer_addr),
            NetworkPathId(active_network_path_id),
        );

        Self {
            network_paths,
            paths,
            max_concurrent_network_paths,
            max_concurrent_paths,
            addrs_to_paths,
            events: VecDeque::new(),
            is_server,
            multipath: false,
            path_abandon: VecDeque::new(),
            path_status_to_advertise: VecDeque::new(),
            next_path_status_seq_num: 0,
        }
    }

    /// Gets an immutable reference to the path identified by `path_id`. If the
    /// provided `path_id` does not identify any current `Path`, returns an
    /// [`InvalidState`].
    ///
    /// [`InvalidState`]: enum.Error.html#variant.InvalidState
    #[inline]
    pub fn get(&self, path_id: InternalPathId) -> Result<&Path> {
        self.paths.get(path_id.0).ok_or(Error::InvalidState)
    }

    /// Gets a mutable reference to the path identified by `path_id`. If the
    /// provided `path_id` does not identify any current `Path`, returns an
    /// [`InvalidState`].
    ///
    /// [`InvalidState`]: enum.Error.html#variant.InvalidState
    #[inline]
    pub fn get_mut(&mut self, path_id: InternalPathId) -> Result<&mut Path> {
        self.paths.get_mut(path_id.0).ok_or(Error::InvalidState)
    }

    /// Gets a mutable reference to both the `Path` (with corresponding path id)
    /// and its active `NetworkPath`.
    #[inline]
    pub fn get_mut_with_active(
        &mut self, path_id: InternalPathId,
    ) -> Result<(&mut Path, &mut NetworkPath)> {
        let p = self.paths.get_mut(path_id.0).ok_or(Error::InvalidState)?;
        let np = self
            .network_paths
            .get_mut(p.network_path_id.0)
            .ok_or(Error::InvalidState)?;
        Ok((p, np))
    }

    /// Gets a mutable reference to both the `Path` and the active `NetworkPath`
    /// associated to their provided IDs.
    ///
    /// [`InvalidState`]: enum.Error.html#variant.InvalidState
    pub fn get_both_mut(
        &mut self, path_id: InternalPathId, network_path_id: NetworkPathId,
    ) -> Result<(&mut Path, &mut NetworkPath)> {
        let p = self.paths.get_mut(path_id.0).ok_or(Error::InvalidState)?;
        let np = self
            .network_paths
            .get_mut(network_path_id.0)
            .ok_or(Error::InvalidState)?;
        Ok((p, np))
    }

    /// Gets an immutable reference to the network path identified by
    /// `network_path_id`. If the provided `network_path_id` does not identify
    /// any current `NetworkPath`, returns an [`InvalidState`].
    ///
    /// [`InvalidState`]: enum.Error.html#variant.InvalidState
    #[inline]
    pub fn get_network(
        &self, network_path_id: NetworkPathId,
    ) -> Result<&NetworkPath> {
        self.network_paths
            .get(network_path_id.0)
            .ok_or(Error::InvalidState)
    }

    /// Gets a mutable reference to the path identified by `network_path_id`. If
    /// the provided `network_path_id` does not identify any current
    /// `NetworkPath`, returns an [`InvalidState`].
    ///
    /// [`InvalidState`]: enum.Error.html#variant.InvalidState
    #[inline]
    pub fn get_network_mut(
        &mut self, network_path_id: NetworkPathId,
    ) -> Result<&mut NetworkPath> {
        self.network_paths
            .get_mut(network_path_id.0)
            .ok_or(Error::InvalidState)
    }

    /// Gets an immutable reference to any possible active path. This method
    /// should be avoided when possible.
    #[inline]
    pub fn get_any_active(&self) -> Result<(&Path, &NetworkPath)> {
        self.paths
            .iter()
            .find_map(|(_, p)| {
                self.get_network(p.network_path_id).ok().and_then(|np| {
                    p.active(p.network_path_id, np).then_some((p, np))
                })
            })
            .ok_or(Error::InvalidState)
    }

    /// Gets a mutable reference to any possible active path. This method
    /// should be avoided when possible.
    #[inline]
    pub fn get_any_active_mut(&mut self) -> Result<(&mut Path, &NetworkPath)> {
        self.paths
            .iter_mut()
            .find_map(|(_, p)| {
                self.network_paths.get(p.network_path_id.0).and_then(|np| {
                    p.active(p.network_path_id, np).then_some((p, np))
                })
            })
            .ok_or(Error::InvalidState)
    }

    /// Returns an iterator over all existing paths.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (InternalPathId, &Path)> {
        self.paths.iter().map(|(ipid, p)| (InternalPathId(ipid), p))
    }

    /// Returns a mutable iterator over all existing paths.
    #[inline]
    pub fn iter_mut(
        &mut self,
    ) -> impl Iterator<Item = (InternalPathId, &mut Path)> {
        self.paths
            .iter_mut()
            .map(|(ipid, p)| (InternalPathId(ipid), p))
    }

    /// Returns a mutable iterator over all existing paths and their active
    /// network one.
    #[inline]
    pub fn iter_mut_with_active_network(
        &mut self,
    ) -> impl Iterator<Item = (InternalPathId, (&mut Path, &NetworkPath))> {
        self.paths.iter_mut().filter_map(|(ipid, p)| {
            self.network_paths
                .get(p.network_path_id().0)
                .map(|np| (InternalPathId(ipid), (p, np)))
        })
    }

    /// Returns an iterator over all existing network paths.
    #[inline]
    pub fn network_iter(
        &self,
    ) -> impl Iterator<Item = (NetworkPathId, &NetworkPath)> {
        self.network_paths
            .iter()
            .map(|(npid, np)| (NetworkPathId(npid), np))
    }

    /// Returns a mutable iterator over all existing network paths.
    #[inline]
    pub fn network_iter_mut(
        &mut self,
    ) -> impl Iterator<Item = (NetworkPathId, &mut NetworkPath)> {
        self.network_paths
            .iter_mut()
            .map(|(npid, np)| (NetworkPathId(npid), np))
    }

    /// Returns the number of existing network paths.
    #[inline]
    #[cfg(test)]
    pub fn network_len(&self) -> usize {
        self.network_paths.len()
    }

    /// Returns the number of existing paths.
    #[inline]
    pub fn len(&self) -> usize {
        self.paths.len()
    }

    /// Returns the `NetworkPath` identifier related to the provided `addrs`.
    #[inline]
    pub fn network_path_id_from_addrs(
        &self, addrs: &(SocketAddr, SocketAddr),
    ) -> Option<NetworkPathId> {
        self.addrs_to_paths.get(addrs).copied()
    }

    /// Returns the internal `Path` identifier related to the explicit
    /// PathId.
    #[inline]
    pub fn pid_from_path_id(&self, path_id: PathId) -> Option<InternalPathId> {
        self.paths
            .iter()
            .find(|(_, p)| p.path_id() == path_id)
            .map(|(pid, _)| InternalPathId(pid))
    }

    /// Checks if creating a new network path will not exceed the current
    /// `self.network_paths` capacity. If yes, this method tries to remove one
    /// unused network path. If it fails to do so, returns [`Done`].
    ///
    /// [`Done`]: enum.Error.html#variant.Done
    fn make_room_for_new_network_path(&mut self) -> Result<()> {
        if self.network_paths.len() < self.max_concurrent_network_paths {
            return Ok(());
        }

        let (npid_to_remove, _) = self
            .network_paths
            .iter()
            .find(|(_, np)| np.unused())
            .ok_or(Error::Done)?;

        let network_path = self.network_paths.remove(npid_to_remove);
        self.addrs_to_paths
            .remove(&(network_path.local_addr, network_path.peer_addr));

        Ok(())
    }

    /// Checks if creating a new path will not exceed the current `self.paths`
    /// capacity. If yes, this method tries to remove one unused path. If it
    /// fails to do so, returns [`Done`].
    ///
    /// [`Done`]: enum.Error.html#variant.Done
    fn make_room_for_new_path(&mut self) -> Result<()> {
        if self.paths.len() < self.max_concurrent_paths {
            return Ok(());
        }

        let (pid_to_remove, _) = self
            .paths
            .iter()
            .find(|(_, p)| p.closed())
            .ok_or(Error::Done)?;

        self.paths.remove(pid_to_remove);
        Ok(())
    }

    /// Adds or remove the internal path ID from the set of paths requiring
    /// sending a PATH_ABANDON frame.
    fn mark_path_abandon(&mut self, path_id: InternalPathId, abandon: bool) {
        if abandon {
            // Do not push twice the same identifier.
            if !self.path_abandon.contains(&path_id) {
                self.path_abandon.push_back(path_id);
            }
        } else {
            self.path_abandon.retain(|p| *p != path_id);
        }
    }

    /// Returns the Path ID that should be advertised in the next PATH_ABANDON
    /// frame.
    pub fn path_abandon(&self) -> Option<InternalPathId> {
        self.path_abandon.front().copied()
    }

    /// Returns true if there are any paths that need to send PATH_ABANDON
    /// frames.
    pub fn has_path_abandon(&self) -> bool {
        !self.path_abandon.is_empty()
    }

    /// Records the provided `NetworkPath` and returns its assigned identifier.
    ///
    /// On success, this method takes care of creating a notification to the
    /// serving application, if it serves a server-side connection.
    ///
    /// If there are already `max_concurrent_network_paths` currently recorded,
    /// this method tries to remove an unused `NetworkPath` first. If it fails
    /// to do so, it returns [`Done`].
    ///
    /// [`Done`]: enum.Error.html#variant.Done
    pub fn insert_network_path(
        &mut self, network_path: NetworkPath, related_path_id: Option<PathId>,
        is_server: bool,
    ) -> Result<NetworkPathId> {
        self.make_room_for_new_network_path()?;

        let local_addr = network_path.local_addr;
        let peer_addr = network_path.peer_addr;

        let network_path_id =
            NetworkPathId(self.network_paths.insert(network_path));
        self.addrs_to_paths
            .insert((local_addr, peer_addr), network_path_id);

        // Notifies the application if we are in server mode.
        if is_server {
            if let Some(path_id) = related_path_id {
                self.notify_event(path_id, PathEvent::New(local_addr, peer_addr));
            }
        }

        Ok(network_path_id)
    }

    /// Records the provided `Path` and returns its assigned identifier.
    ///
    /// On success, this method takes care of creating a notification to the
    /// serving application, if it serves a server-side connection.
    ///
    /// If there are already `max_concurrent_paths` currently recorded, this
    /// method tries to remove a closed `Path` first. If it fails to do so,
    /// it returns [`Done`].
    ///
    /// [`Done`]: enum.Error.html#variant.Done
    pub fn insert_path(&mut self, path: Path) -> Result<InternalPathId> {
        self.make_room_for_new_path()?;

        Ok(InternalPathId(self.paths.insert(path)))
    }

    /// Notifies a path event to the application served by the connection.
    pub fn notify_event(&mut self, path_id: PathId, ev: PathEvent) {
        self.events.push_back((path_id, ev));
    }

    /// Gets the first path event to be notified to the application.
    pub fn pop_event(&mut self) -> Option<(PathId, PathEvent)> {
        self.events.pop_front()
    }

    /// Notifies all failed validations to the application.
    pub fn notify_failed_validations(&mut self) {
        let validation_failed = self
            .network_paths
            .iter_mut()
            .filter(|(_, np)| np.validation_failed() && !np.failure_notified);

        for (_, np) in validation_failed {
            // Send an event to all the Path ID that have used the network path.
            for (_, pc) in np.active_dcid_seqs.iter() {
                self.events.push_back((
                    pc.0,
                    PathEvent::FailedValidation(np.local_addr, np.peer_addr),
                ));
            }

            np.failure_notified = true;
        }
    }

    pub fn notify_closed_paths(&mut self) {
        let paths = &mut self.paths;
        let network_paths = &self.network_paths;
        let events = &mut self.events;
        for (_, p) in paths
            .iter_mut()
            .filter(|(_, p)| p.closed() && !p.closure_notified)
        {
            if let PathState::Closed(e) = &p.state {
                if let Some(np) = network_paths.get(p.network_path_id.0) {
                    events.push_back((
                        p.path_id(),
                        PathEvent::Closed(np.local_addr, np.peer_addr, *e),
                    ));
                    p.closure_notified = true;
                }
            }
        }
    }

    /// Finds a network path candidate to be active for a given Path ID and
    /// returns its identifier.
    pub fn find_candidate_network_path(
        &self, path_id: PathId,
    ) -> Option<NetworkPathId> {
        // TODO: also consider unvalidated paths if there are no more validated.
        self.network_paths
            .iter()
            .find(|(_, np)| np.usable_for(path_id))
            .map(|(npid, _)| NetworkPathId(npid))
    }

    /// Returns whether backup paths should be considered to send data packets.
    pub fn consider_backup_paths(&self) -> bool {
        self.iter()
            .filter(|(_, p)| !p.is_backup() && p.recovery.pto_count() == 0)
            .count() ==
            0
    }

    /// Whether there are other paths that can be considered to send non-probing
    /// frames beyond the provided one.
    pub fn has_other_active_than(&self, path_id: PathId) -> bool {
        self.iter().any(|(_, p)| {
            p.path_id() != path_id &&
                !p.potentially_lost() &&
                self.network_paths
                    .get(p.network_path_id.0)
                    .is_some_and(|np| p.active(p.network_path_id, np))
        })
    }

    /// Handles incoming PATH_RESPONSE data.
    pub fn on_response_received(&mut self, data: [u8; 8]) -> Result<()> {
        let challenge_pending = self
            .network_iter_mut()
            .find(|(_, np)| np.has_pending_challenge(data));

        if let Some((_, np)) = challenge_pending {
            if let Some(validated_on_path_id) = np.on_response_received(data) {
                let local_addr = np.local_addr;
                let peer_addr = np.peer_addr;
                let was_migrating = np.migrating;

                np.migrating = false;

                // Notifies the application.
                self.notify_event(
                    validated_on_path_id,
                    PathEvent::Validated(local_addr, peer_addr),
                );

                // If this path was the candidate for migration, notifies the
                // application.
                if was_migrating {
                    self.notify_event(
                        validated_on_path_id,
                        PathEvent::PeerMigrated(local_addr, peer_addr),
                    );
                }
            }
        }
        Ok(())
    }

    /// Handles acknowledged PATH_ABANDONs.
    pub fn on_path_abandon_acknowledged(
        &mut self, abandon_path_id: PathId, now: time::Instant, trace_id: &str,
    ) -> (usize, usize) {
        let mut lost_info = (0, 0);
        if let Some(abandon_pid) = self.pid_from_path_id(abandon_path_id) {
            let path = match self.paths.get_mut(abandon_pid.0) {
                Some(p) => p,
                None => return lost_info,
            };
            let path_id = path.path_id();

            let to_notify = if let PathState::Closing(e) = &mut path.state {
                let to_notify = Some(*e);
                path.state = PathState::Closed(*e);
                to_notify
            } else {
                None
            };

            let lost_info_path =
                path.recovery.mark_all_inflight_as_lost(now, trace_id);
            lost_info.0 += lost_info_path.0;
            lost_info.1 += lost_info_path.1;

            // Iterate on all network paths to remove potential active DCIDs.
            for (_, np) in self.network_paths.iter_mut() {
                {
                    np.active_dcid_seqs.retain(|_, pc| pc.0 != path_id);
                }
            }

            if let Some(np) = self.network_paths.get_mut(path.network_path_id.0) {
                let local_addr = np.local_addr;
                let peer_addr = np.peer_addr;
                if let Some(e) = to_notify {
                    self.notify_event(
                        path_id,
                        PathEvent::Closed(local_addr, peer_addr, e),
                    );
                }
            }
        }

        lost_info
    }

    /// Returns the number of active paths.
    fn active_paths_count(&self) -> usize {
        self.paths
            .iter()
            .filter(|(_, p)| {
                self.get_network(p.network_path_id)
                    .ok()
                    .is_some_and(|np| p.active(p.network_path_id, np))
            })
            .count()
    }

    /// Handles incoming PATH_ABANDONs.
    pub fn on_path_abandon_received(
        &mut self, abandon_path_id: PathId, error_code: u64, trace_id: &str,
    ) -> Result<()> {
        let is_server = self.is_server;

        let abandon_pid = match self.pid_from_path_id(abandon_path_id) {
            Some(pid) => pid,
            None => {
                warn!(
                    "{} received PATH_ABANDON for unknown path_id {}; ignoring",
                    trace_id, abandon_path_id
                );
                return Ok(());
            },
        };

        let active_paths_count = self.active_paths_count();
        let abandon_path = self.get_mut(abandon_pid)?;
        // If the path was already closed, just close it.
        if abandon_path.closed() {
            return Ok(());
        }
        // If we are the server, and receiving a PATH_ABANDON for the only
        // active path, request a connection closure.
        if is_server && active_paths_count == 1 {
            return Err(Error::UnavailablePath);
        }
        let was_closing = abandon_path.is_closing();
        abandon_path.set_state(PathState::Closing(error_code))?;
        abandon_path.on_abandon_received();
        if !was_closing {
            self.mark_path_abandon(abandon_pid, true);
        }

        Ok(())
    }

    /// Handles the sending of PATH_ABANDONs.
    pub fn on_path_abandon_sent(
        &mut self, abandon_path_id: InternalPathId, now: time::Instant,
    ) -> Result<()> {
        let abandoned_path = self
            .paths
            .get_mut(abandon_path_id.0)
            .ok_or(Error::InvalidState)?;
        let abandoned_network_path = self
            .network_paths
            .get(abandoned_path.network_path_id().0)
            .ok_or(Error::InvalidState)?;
        abandoned_path.closing_timer = Some(now + abandoned_network_path.pto());
        self.mark_path_abandon(abandon_path_id, false);
        Ok(())
    }

    /// Returns whether multipath extension has been enabled.
    pub fn multipath(&self) -> bool {
        self.multipath
    }

    /// Sets whether multipath extension is enabled.
    pub fn set_multipath(&mut self, v: bool) {
        self.multipath = v;
    }

    /// Returns the number of active paths.
    fn count_active_paths(&self) -> usize {
        self.paths
            .iter()
            .filter(|(_, p)| {
                self.get_network(p.network_path_id)
                    .ok()
                    .is_some_and(|np| p.active(p.network_path_id, np))
            })
            .count()
    }

    /// Changes the state of the path with the identifier `path_id` according to
    /// the provided `PathRequest`.
    ///
    /// This API is only usable when multipath extensions are enabled.
    /// Otherwise, it raises an [`InvalidState`].
    ///
    /// In case the request closes the last active path, returns a
    /// [`NoMorePath`].
    ///
    /// In case the request is invalid, returns an [`InvalidState`].
    ///
    /// [`InvalidState`]: enum.Error.html#variant.InvalidState
    /// [`NoMorePath`]: enum.Error.html#variant.NoMorePath
    pub fn request(
        &mut self, path_id: PathId, request: PathRequest,
    ) -> Result<()> {
        if !self.multipath {
            return Err(Error::InvalidState);
        }
        let pid = self.pid_from_path_id(path_id).ok_or(Error::InvalidState)?;
        let requested_state = request.requested_state();
        if let PathState::Closing(_) = requested_state {
            if self.count_active_paths() == 1 {
                let p = self.get(pid)?;
                let np = self.get_network(p.network_path_id)?;
                if p.active(p.network_path_id, np) {
                    return Err(Error::NoMorePath);
                }
            }
        }
        let path = self.get_mut(pid)?;
        path.set_state(requested_state)?;
        if path.is_closing() {
            self.mark_path_abandon(pid, true);
        }
        Ok(())
    }

    /// Sets the network path with identifier 'network_path_id' to be the active
    /// network path for the given PathId.
    ///
    /// When multipath extensions are disabled, there can be exactly one active
    /// path on which non-probing packets can be sent. If another path is marked
    /// as active, it will be superseeded by the one having `path_id` as
    /// identifier.
    ///
    /// A server should always ensure that the active path is validated. If it
    /// is already the case, when the multipath extensions are disabled, it
    /// notifies the application that the connection migrated. Otherwise, it
    /// triggers a path validation and, if multipath extensions are disabled,
    /// defers the notification once it is actually validated.
    ///
    /// When multipath extensions are enabled, this call is equivalent to
    /// calling [`request()`] with `PathRequest::Active`.
    ///
    /// [`request()`]: struct.PathManager.html#method.request
    pub fn set_active_network_path(
        &mut self, pid: InternalPathId, network_path_id: NetworkPathId,
    ) -> Result<()> {
        let is_server = self.is_server;
        let multipath = self.multipath;

        let np = self.get_network(network_path_id)?;
        // The network path may not have any DCID assigned. This can be done
        // later.
        if !np.working() {
            return Err(Error::UnavailablePath);
        }

        let p = self.paths.get_mut(pid.0).ok_or(Error::InvalidState)?;
        let path_id = p.path_id();

        if !multipath && path_id != 0 {
            return Err(Error::InvalidState);
        }

        p.network_path_id = network_path_id;

        if is_server {
            let np = self.get_network_mut(network_path_id)?;
            if np.validated() {
                let local_addr = np.local_addr();
                let peer_addr = np.peer_addr();
                self.notify_event(
                    path_id,
                    PathEvent::PeerMigrated(local_addr, peer_addr),
                );
            } else {
                np.migrating = true;
                // Requests path validation if needed.
                if !np.under_validation() {
                    np.request_validation();
                }
            }
        }

        Ok(())
    }

    /// Returns whether a DCID has been assigned on the network path with
    /// identifier network_path_id to send packets belonging to the QUIC
    /// path with identifier path id.
    pub fn has_dcid(
        &self, path_id: PathId, network_path_id: NetworkPathId,
    ) -> bool {
        match self.get_network(network_path_id) {
            Ok(np) => np.active_dcid_seqs.iter().any(|(_, pc)| pc.0 == path_id),
            _ => false,
        }
    }

    /// Returns network paths identifiers that should have a
    /// new DCID associated (and to which QUIC path).
    pub fn network_path_ids_without_dcid(
        &self,
    ) -> SmallVec<[(NetworkPathId, PathId); 1]> {
        self.paths
            .iter()
            .map(|(_, p)| (p.network_path_id, p.path_id))
            .filter(|(npid, path_id)| !self.has_dcid(*path_id, *npid))
            .collect()
    }

    /// Returns network paths identifiers whose validation was requested, but
    /// that do not have any DCID.
    pub fn network_path_ids_without_dcid_needing_validation(
        &self,
    ) -> SmallVec<[NetworkPathId; 1]> {
        self.network_iter()
            .filter(|(_, np)| {
                np.validation_requested() && np.active_dcid_seqs.is_empty()
            })
            .map(|(npid, _)| npid)
            .collect()
    }

    /// Returns whether the Path identified by ipid is active on some network
    /// path.
    pub fn is_active(&self, ipid: InternalPathId) -> bool {
        if let Ok(p) = self.get(ipid) {
            if p.state != PathState::Active {
                return false;
            }
            if let Ok(np) = self.get_network(p.network_path_id()) {
                return np.dcid_seq_for_path_id(p.path_id()).is_some();
            }
        }

        false
    }

    /// Sets the provided `status` on the path identified by `path_id`.
    pub fn set_path_status(
        &mut self, path_id: PathId, status: PathStatus,
    ) -> Result<()> {
        let pid = self.pid_from_path_id(path_id).ok_or(Error::UnknownPath)?;
        self.get_mut(pid)?.status = status;
        Ok(())
    }

    /// Requests the advertisement of a path status.
    pub fn advertise_path_status(&mut self, path_id: PathId) -> Result<()> {
        let pid = self.pid_from_path_id(path_id).ok_or(Error::UnknownPath)?;
        let status = self.get(pid)?.status;
        self.path_status_to_advertise.push_back((
            path_id,
            self.next_path_status_seq_num,
            status.into(),
        ));
        self.next_path_status_seq_num += 1;
        Ok(())
    }

    /// Returns true if the host should send a PATH_STATUS frame.
    #[inline]
    pub fn has_path_status(&self) -> bool {
        !self.path_status_to_advertise.is_empty()
    }

    /// Returns the Path ID, the sequence number and the availability
    /// status (PATH_BACKUP or PATH_AVAILABLE) that should be advertised next.
    pub fn path_status(&self) -> Option<(PathId, u64, bool)> {
        self.path_status_to_advertise.front().copied()
    }

    /// Handles the sending of PATH_BACKUP/PATH_AVAILABLE.
    pub fn on_path_status_sent(&mut self) {
        self.path_status_to_advertise.pop_front();
    }

    /// Are all paths in backup state?
    pub fn all_available_paths_backup(&self) -> bool {
        !self
            .paths
            .iter()
            .filter(|(_, p)| {
                self.get_network(p.network_path_id)
                    .ok()
                    .is_some_and(|np| p.active(p.network_path_id, np))
            })
            .any(|p| !p.1.is_backup())
    }

    /// Handles the reception of PATH_BACKUP/PATH_AVAILABLE.
    pub fn on_path_status_received(
        &mut self, path_id: PathId, seq_num: u64, available: bool,
    ) {
        let pid = match self.pid_from_path_id(path_id) {
            Some(p) => p,
            None => return,
        };
        if let Some(p) = self.paths.get_mut(pid.0) {
            if seq_num >= p.expected_path_status_seq_num {
                p.expected_path_status_seq_num = seq_num.saturating_add(1);
                let path_id = p.path_id();
                // TODO: remove this.
                if let Some(np) = self.network_paths.get(p.network_path_id.0) {
                    let addr = (np.local_addr(), np.peer_addr());
                    self.notify_event(
                        path_id,
                        PathEvent::PeerPathStatus(addr, available.into()),
                    );
                }
            }
        }
    }

    /// Updates the PMTUD probe of a NetworkPath with the provided value.
    ///
    /// It also updates the recovery of paths that actively rely on the updated
    /// network path.
    ///
    /// On success, returns the old MTU, the new one and whether the update is
    /// done for each concerned QUIC path.
    pub fn update_pmtud_value(
        &mut self, npid: NetworkPathId, mtu_probe: usize, trace_id: &str,
    ) -> Result<SmallVec<[PmtudUpdate; 1]>> {
        let mut updates = SmallVec::new();
        let np = self
            .network_paths
            .get_mut(npid.0)
            .ok_or(Error::UnknownPath)?;
        let pmtud_next = np.pmtud.get_current();
        np.pmtud.set_current(cmp::max(pmtud_next, mtu_probe));

        // Stop sending path MTU probes after successful probe.
        np.pmtud.should_probe(false);

        trace!(
            "{} pmtud acked; pmtu size {:?}",
            trace_id,
            np.pmtud.get_current()
        );

        let new = np.pmtud.get_current();
        let done = Some(true);

        // Iterate over paths and update the recovery of the ones using the
        // updated network path.
        for (_, p) in self.paths.iter_mut() {
            if p.network_path_id == npid {
                trace!(
                    "{} path id {}: updating pmtu {:?}",
                    trace_id,
                    p.path_id(),
                    new,
                );

                p.recovery.pmtud_update_max_datagram_size(new);

                updates.push((
                    Some(p.recovery.max_datagram_size() as u16),
                    new as u16,
                    done,
                ));
            }
        }

        Ok(updates)
    }
}

/// Statistics about the path of a connection.
///
/// A connection’s path statistics can be collected using the [`path_stats()`]
/// method.
///
/// [`path_stats()`]: struct.Connection.html#method.path_stats
#[derive(Clone)]
pub struct PathStats {
    /// The explicit path ID of the path, if doing multipath.
    pub path_id: PathId,

    /// The local address of the path.
    pub local_addr: SocketAddr,

    /// The peer address of the path.
    pub peer_addr: SocketAddr,

    /// The path validation state.
    pub validation_state: NetworkPathValidationState,

    /// The path state.
    pub state: PathState,

    /// Is it active?
    pub active: bool,

    /// The number of QUIC packets received.
    pub recv: usize,

    /// The number of QUIC packets sent.
    pub sent: usize,

    /// The number of QUIC packets that were lost.
    pub lost: usize,

    /// The number of QUIC packets that were spuriously marked as lost.
    pub lost_spurious: usize,

    /// The number of sent QUIC packets with retransmitted data.
    pub retrans: usize,

    /// The number of DATAGRAM frames received.
    pub dgram_recv: usize,

    /// The number of DATAGRAM frames sent.
    pub dgram_sent: usize,

    /// The estimated round-trip time of the connection.
    pub rtt: time::Duration,

    /// The minimum round-trip time observed.
    pub min_rtt: Option<time::Duration>,

    /// The estimated round-trip time variation in samples using a mean
    /// variation.
    pub rttvar: time::Duration,

    /// The number of round-trip time updates over that path.
    pub rtt_update: usize,

    /// The size of the connection's congestion window in bytes.
    pub cwnd: usize,

    /// The number of sent bytes.
    pub sent_bytes: u64,

    /// The number of received bytes.
    pub recv_bytes: u64,

    /// The number of bytes lost.
    pub lost_bytes: u64,

    /// The number of stream bytes retransmitted.
    pub stream_retrans_bytes: u64,

    /// The current PMTU for the connection.
    pub pmtu: usize,

    /// The most recent data delivery rate estimate in bytes/s.
    ///
    /// Note that this value could be inaccurate if the application does not
    /// respect pacing hints (see [`SendInfo.at`] and [Pacing] for more
    /// details).
    ///
    /// [`SendInfo.at`]: struct.SendInfo.html#structfield.at
    /// [Pacing]: index.html#pacing
    pub delivery_rate: u64,

    /// The current PTO count.
    pub pto_count: u32,
}

impl std::fmt::Debug for PathStats {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "path_id={:x} local_addr={:?} peer_addr={:?} ",
            self.path_id, self.local_addr, self.peer_addr,
        )?;
        write!(
            f,
            "validation_state={:?} state={:?} ",
            self.validation_state, self.state,
        )?;
        write!(
            f,
            "recv={} sent={} lost={} lost_spurious={} retrans={} rtt={:?} min_rtt={:?} rttvar={:?} rtt_update={} cwnd={}",
            self.recv, self.sent, self.lost, self.lost_spurious, self.retrans, self.rtt, self.min_rtt, self.rttvar, self.rtt_update, self.cwnd,
        )?;

        write!(
            f,
            " sent_bytes={} recv_bytes={} lost_bytes={}",
            self.sent_bytes, self.recv_bytes, self.lost_bytes,
        )?;

        write!(
            f,
            " stream_retrans_bytes={} pmtu={} delivery_rate={} pto_count={}",
            self.stream_retrans_bytes,
            self.pmtu,
            self.delivery_rate,
            self.pto_count,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::rand;
    use crate::MIN_CLIENT_INITIAL_LEN;

    use crate::recovery::RecoveryConfig;
    use crate::Config;

    use super::*;

    #[test]
    fn path_validation_limited_mtu() {
        let client_addr = "127.0.0.1:1234".parse().unwrap();
        let client_addr_2 = "127.0.0.1:5678".parse().unwrap();
        let server_addr = "127.0.0.1:4321".parse().unwrap();

        let config = Config::new(crate::PROTOCOL_VERSION).unwrap();
        let recovery_config = RecoveryConfig::from_config(&config);

        let network_path = NetworkPath::new(
            client_addr,
            server_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            true,
            &recovery_config,
        );
        let path = Path::new(
            0,
            NetworkPathId(0), // later overwritten
            &recovery_config,
        );
        let mut path_mgr =
            PathMap::new(network_path, path, 2, 2, false, true, 1200);

        let probed_network_path = NetworkPath::new(
            client_addr_2,
            server_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            false,
            &recovery_config,
        );
        path_mgr
            .insert_network_path(probed_network_path, Some(0), false)
            .unwrap();

        let npid = path_mgr
            .network_path_id_from_addrs(&(client_addr_2, server_addr))
            .unwrap();
        path_mgr.get_network_mut(npid).unwrap().request_validation();
        assert!(path_mgr
            .get_network_mut(npid)
            .unwrap()
            .validation_requested());
        assert!(path_mgr.get_network_mut(npid).unwrap().probing_required());

        // Fake sending of PathChallenge in a packet of MIN_CLIENT_INITIAL_LEN - 1
        // bytes.
        let data = rand::rand_u64().to_be_bytes();
        path_mgr.get_network_mut(npid).unwrap().add_challenge_sent(
            data,
            0,
            MIN_CLIENT_INITIAL_LEN - 1,
            time::Instant::now(),
        );

        assert!(!path_mgr
            .get_network_mut(npid)
            .unwrap()
            .validation_requested());
        assert!(!path_mgr.get_network_mut(npid).unwrap().probing_required());
        assert!(path_mgr.get_network_mut(npid).unwrap().under_validation());
        assert!(!path_mgr.get_network_mut(npid).unwrap().validated());
        assert_eq!(
            path_mgr.get_network_mut(npid).unwrap().validation_state,
            NetworkPathValidationState::Validating
        );
        assert_eq!(path_mgr.pop_event(), None);

        // Receives the response. The path is reachable, but the MTU is not
        // validated yet.
        path_mgr.on_response_received(data).unwrap();

        assert!(path_mgr
            .get_network_mut(npid)
            .unwrap()
            .validation_requested());
        assert!(path_mgr.get_network_mut(npid).unwrap().probing_required());
        assert!(path_mgr.get_network_mut(npid).unwrap().under_validation());
        assert!(!path_mgr.get_network_mut(npid).unwrap().validated());
        assert_eq!(
            path_mgr.get_network_mut(npid).unwrap().validation_state,
            NetworkPathValidationState::ValidatingMTU
        );
        assert_eq!(path_mgr.pop_event(), None);

        // Fake sending of PathChallenge in a packet of MIN_CLIENT_INITIAL_LEN
        // bytes.
        let data = rand::rand_u64().to_be_bytes();
        path_mgr.get_network_mut(npid).unwrap().add_challenge_sent(
            data,
            0,
            MIN_CLIENT_INITIAL_LEN,
            time::Instant::now(),
        );

        path_mgr.on_response_received(data).unwrap();

        assert!(!path_mgr
            .get_network_mut(npid)
            .unwrap()
            .validation_requested());
        assert!(!path_mgr.get_network_mut(npid).unwrap().probing_required());
        assert!(!path_mgr.get_network_mut(npid).unwrap().under_validation());
        assert!(path_mgr.get_network_mut(npid).unwrap().validated());
        assert_eq!(
            path_mgr.get_network_mut(npid).unwrap().validation_state,
            NetworkPathValidationState::Validated
        );
        assert_eq!(
            path_mgr.pop_event(),
            Some((0, PathEvent::Validated(client_addr_2, server_addr)))
        );
    }

    #[test]
    fn multiple_probes() {
        let client_addr = "127.0.0.1:1234".parse().unwrap();
        let server_addr = "127.0.0.1:4321".parse().unwrap();

        let config = Config::new(crate::PROTOCOL_VERSION).unwrap();
        let recovery_config = RecoveryConfig::from_config(&config);

        let network_path = NetworkPath::new(
            client_addr,
            server_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            true,
            &recovery_config,
        );
        let path = Path::new(
            0,
            NetworkPathId(0), // later overwritten
            &recovery_config,
        );
        let mut client_path_mgr =
            PathMap::new(network_path, path, 2, 2, false, false, 1200);
        let mut server_network_path = NetworkPath::new(
            server_addr,
            client_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            false,
            &recovery_config,
        );

        let client_npid = client_path_mgr
            .network_path_id_from_addrs(&(client_addr, server_addr))
            .unwrap();

        // First probe.
        let data = rand::rand_u64().to_be_bytes();

        client_path_mgr
            .get_network_mut(client_npid)
            .unwrap()
            .add_challenge_sent(
                data,
                0,
                MIN_CLIENT_INITIAL_LEN,
                time::Instant::now(),
            );

        // Second probe.
        let data_2 = rand::rand_u64().to_be_bytes();

        client_path_mgr
            .get_network_mut(client_npid)
            .unwrap()
            .add_challenge_sent(
                data_2,
                0,
                MIN_CLIENT_INITIAL_LEN,
                time::Instant::now(),
            );
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            2
        );

        // If we receive multiple challenges, we can store them.
        server_network_path.on_challenge_received(data);
        assert_eq!(server_network_path.received_challenges.len(), 1);
        server_network_path.on_challenge_received(data_2);
        assert_eq!(server_network_path.received_challenges.len(), 2);

        // Response for first probe.
        client_path_mgr.on_response_received(data).unwrap();
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            1
        );

        // Response for second probe.
        client_path_mgr.on_response_received(data_2).unwrap();
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            0
        );
    }

    #[test]
    fn too_many_probes() {
        let client_addr = "127.0.0.1:1234".parse().unwrap();
        let server_addr = "127.0.0.1:4321".parse().unwrap();

        // Default to DEFAULT_MAX_PATH_CHALLENGE_RX_QUEUE_LEN
        let config = Config::new(crate::PROTOCOL_VERSION).unwrap();
        let recovery_config = RecoveryConfig::from_config(&config);

        let network_path = NetworkPath::new(
            client_addr,
            server_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            true,
            &recovery_config,
        );
        let path = Path::new(
            0,
            NetworkPathId(0), // later overwritten
            &recovery_config,
        );
        let mut client_path_mgr =
            PathMap::new(network_path, path, 2, 2, false, false, 1200);
        let mut server_network_path = NetworkPath::new(
            server_addr,
            client_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            false,
            &recovery_config,
        );

        let client_npid = client_path_mgr
            .network_path_id_from_addrs(&(client_addr, server_addr))
            .unwrap();

        // First probe.
        let data = rand::rand_u64().to_be_bytes();

        client_path_mgr
            .get_network_mut(client_npid)
            .unwrap()
            .add_challenge_sent(
                data,
                0,
                MIN_CLIENT_INITIAL_LEN,
                time::Instant::now(),
            );

        // Second probe.
        let data_2 = rand::rand_u64().to_be_bytes();

        client_path_mgr
            .get_network_mut(client_npid)
            .unwrap()
            .add_challenge_sent(
                data_2,
                0,
                MIN_CLIENT_INITIAL_LEN,
                time::Instant::now(),
            );
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            2
        );

        // Third probe.
        let data_3 = rand::rand_u64().to_be_bytes();

        client_path_mgr
            .get_network_mut(client_npid)
            .unwrap()
            .add_challenge_sent(
                data_3,
                0,
                MIN_CLIENT_INITIAL_LEN,
                time::Instant::now(),
            );
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            3
        );

        // Fourth probe.
        let data_4 = rand::rand_u64().to_be_bytes();

        client_path_mgr
            .get_network_mut(client_npid)
            .unwrap()
            .add_challenge_sent(
                data_4,
                0,
                MIN_CLIENT_INITIAL_LEN,
                time::Instant::now(),
            );
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            4
        );

        // If we receive multiple challenges, we can store them up to our queue
        // size.
        server_network_path.on_challenge_received(data);
        assert_eq!(server_network_path.received_challenges.len(), 1);
        server_network_path.on_challenge_received(data_2);
        assert_eq!(server_network_path.received_challenges.len(), 2);
        server_network_path.on_challenge_received(data_3);
        assert_eq!(server_network_path.received_challenges.len(), 3);
        server_network_path.on_challenge_received(data_4);
        assert_eq!(server_network_path.received_challenges.len(), 3);

        // Response for first probe.
        client_path_mgr.on_response_received(data).unwrap();
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            3
        );

        // Response for second probe.
        client_path_mgr.on_response_received(data_2).unwrap();
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            2
        );

        // Response for third probe.
        client_path_mgr.on_response_received(data_3).unwrap();
        assert_eq!(
            client_path_mgr
                .get_network(client_npid)
                .unwrap()
                .in_flight_challenges
                .len(),
            1
        );

        // There will never be a response for fourth probe...
    }

    #[test]
    fn path_priority() {
        let client_addr = "127.0.0.1:1234".parse().unwrap();
        let server_addr = "127.0.0.1:4321".parse().unwrap();

        let config = Config::new(crate::PROTOCOL_VERSION).unwrap();
        let recovery_config = RecoveryConfig::from_config(&config);

        let network_path = NetworkPath::new(
            client_addr,
            server_addr,
            config.path_challenge_recv_max_queue_len,
            1200,
            true,
            &recovery_config,
        );
        let path = Path::new(0, NetworkPathId(0), &recovery_config);
        let mut paths = PathMap::new(
            network_path,
            path,
            3,
            3,
            true,
            false,
            MIN_CLIENT_INITIAL_LEN,
        );
        let pid = paths.pid_from_path_id(0).unwrap();
        let npid = paths
            .network_path_id_from_addrs(&(client_addr, server_addr))
            .unwrap();

        let path_2 = Path::new(1, npid, &recovery_config);
        let pid_2 = paths.insert_path(path_2).unwrap();
        let path_3 = Path::new(2, npid, &recovery_config);
        let pid_3 = paths.insert_path(path_3).unwrap();

        assert_eq!(paths.set_path_status(1, PathStatus::Backup), Ok(()));
        assert_eq!(
            paths
                .iter()
                .filter_map(|(pid, p)| p.is_backup().then_some(pid))
                .collect::<Vec<InternalPathId>>(),
            vec![pid_2]
        );
        assert_eq!(
            paths
                .iter()
                .filter_map(|(pid, p)| (!p.is_backup()).then_some(pid))
                .collect::<Vec<InternalPathId>>(),
            vec![pid, pid_3]
        );
        assert_eq!(
            paths.set_path_status(42, PathStatus::Backup),
            Err(Error::UnknownPath)
        );

        // Fake sending of PATH_STATUS frame.
        paths.advertise_path_status(1).unwrap();

        // We can also fake send for another non-backup path.
        paths.advertise_path_status(2).unwrap();

        assert_eq!(paths.has_path_status(), true);
        assert_eq!(paths.path_status(), Some((1, 0, false)));
        paths.on_path_status_sent();
        assert_eq!(paths.has_path_status(), true);
        assert_eq!(paths.path_status(), Some((2, 1, true)));
        paths.on_path_status_sent();
        assert_eq!(paths.has_path_status(), false);
        assert_eq!(paths.path_status(), None);

        assert_eq!(paths.set_path_status(2, PathStatus::Backup), Ok(()));
        assert_eq!(paths.set_path_status(1, PathStatus::Available), Ok(()));
        paths.advertise_path_status(1).unwrap();
        paths.advertise_path_status(2).unwrap();
        assert_eq!(paths.has_path_status(), true);
        assert_eq!(paths.path_status(), Some((1, 2, true)));
        paths.on_path_status_sent();
        assert_eq!(paths.has_path_status(), true);
        assert_eq!(paths.path_status(), Some((2, 3, false)));
        paths.on_path_status_sent();
        assert_eq!(paths.has_path_status(), false);
        assert_eq!(paths.path_status(), None);
    }
}
