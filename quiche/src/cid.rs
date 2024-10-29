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

use smallvec::SmallVec;

use crate::CIDSeq;
use crate::Error;
use crate::FourTuple;
use crate::PathId;
use crate::Result;

use crate::frame;

use crate::packet::ConnectionId;

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::HashSet;
use std::collections::VecDeque;

/// Used to calculate the cap for the queue of retired connection IDs for which
/// a RETIRED_CONNECTION_ID frame have not been sent, as a multiple of
/// `active_conn_id_limit` (see RFC 9000, section 5.1.2).
const RETIRED_CONN_ID_LIMIT_MULTIPLIER: usize = 3;

#[derive(Default)]
struct BoundedConnectionIdSeqSet {
    /// The inner set.
    inner: HashSet<CIDSeq>,

    /// The maximum number of elements that the set can have.
    capacity: usize,
}

impl BoundedConnectionIdSeqSet {
    /// Creates a set bounded by `capacity`.
    fn new(capacity: usize) -> Self {
        Self {
            inner: HashSet::new(),
            capacity,
        }
    }

    fn insert(&mut self, e: u64) -> Result<bool> {
        if self.inner.len() >= self.capacity {
            return Err(Error::IdLimit);
        }

        Ok(self.inner.insert(e))
    }

    fn remove(&mut self, e: &u64) -> bool {
        self.inner.remove(e)
    }

    fn front(&self) -> Option<u64> {
        self.inner.iter().next().copied()
    }

    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

/// A structure holding a `ConnectionId` and all its related metadata.
#[derive(Debug, Default)]
pub struct ConnectionIdEntry {
    /// The Connection ID.
    pub cid: ConnectionId<'static>,

    /// Its associated sequence number.
    pub seq: CIDSeq,

    /// Its associated reset token. Initial CIDs may not have any reset token.
    pub reset_token: Option<u128>,

    /// The 4-tuple on which the CID is in use. Local-peer.
    pub network_path: Option<FourTuple>,
}

trait Identifiable {
    fn id(&self) -> u64;
}

impl Identifiable for ConnectionIdEntry {
    fn id(&self) -> u64 {
        self.seq
    }
}

#[derive(Default)]
struct BoundedNonEmptyVecDeque<T> {
    /// The inner `VecDeque`.
    inner: VecDeque<T>,

    /// The maximum number of elements that the `VecDeque` can have.
    capacity: usize,
}

impl<T: Identifiable> BoundedNonEmptyVecDeque<T> {
    /// Creates a `VecDeque` bounded by `capacity` and inserts
    /// `initial_entry` in it.
    fn new(capacity: usize, initial_entry: T) -> Self {
        let mut inner = VecDeque::with_capacity(1);
        inner.push_back(initial_entry);
        Self { inner, capacity }
    }

    /// Updates the maximum capacity of the inner `VecDeque` to `new_capacity`.
    /// Does nothing if `new_capacity` is lower or equal to the current
    /// `capacity`.
    fn resize(&mut self, new_capacity: usize) {
        if new_capacity > self.capacity {
            self.capacity = new_capacity;
        }
    }

    /// Returns the oldest inserted entry still present in the `VecDeque`.
    fn get_oldest(&self) -> &T {
        self.inner.front().expect("vecdeque is empty")
    }

    /// Gets a immutable reference to the entry having the provided `id`.
    fn get(&self, id: u64) -> Option<&T> {
        // We need to iterate over the whole map to find the key.
        self.inner.iter().find(|e| e.id() == id)
    }

    /// Gets a mutable reference to the entry having the provided `seq`.
    fn get_mut(&mut self, id: u64) -> Option<&mut T> {
        // We need to iterate over the whole map to find the key.
        self.inner.iter_mut().find(|e| e.id() == id)
    }

    /// Returns an iterator over the entries in the `VecDeque`.
    fn iter(&self) -> impl Iterator<Item = &T> {
        self.inner.iter()
    }

    /// Returns a mutable iterator over the entries in the `VecDeque`.
    fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.inner.iter_mut()
    }

    /// Returns the number of elements in the `VecDeque`.
    fn len(&self) -> usize {
        self.inner.len()
    }

    /// Inserts the provided entry in the `VecDeque`.
    ///
    /// This method ensures the unicity of the `id` associated to an entry. If
    /// an entry has the same `id` than `e`, this method updates the entry in
    /// the `VecDeque` and the number of stored elements remains unchanged.
    ///
    /// If inserting a new element would exceed the collection's capacity, this
    /// method raises an [`IdLimit`].
    ///
    /// [`IdLimit`]: enum.Error.html#IdLimit
    fn insert(&mut self, e: T) -> Result<()> {
        // Ensure we don't have duplicates.
        match self.get_mut(e.id()) {
            Some(oe) => *oe = e,
            None => {
                if self.inner.len() >= self.capacity {
                    return Err(Error::IdLimit);
                }
                self.inner.push_back(e);
            },
        };
        Ok(())
    }

    /// Removes all the elements in the collection and inserts the provided one.
    fn clear_and_insert(&mut self, e: T) {
        self.inner.clear();
        self.inner.push_back(e);
    }

    /// Removes the element in the collection having as identifier the provided
    /// `id`.
    ///
    /// If this method is called when there remains a single element in the
    /// collection, this method raises an [`OutOfIdentifiers`].
    ///
    /// Returns `Some` if the element was in the collection and removed, or
    /// `None` if it was not and nothing was modified.
    ///
    /// [`OutOfIdentifiers`]: enum.Error.html#OutOfIdentifiers
    fn remove(&mut self, id: u64, allow_empty: bool) -> Result<Option<T>> {
        if self.inner.len() <= 1 {
            // If we are closing the path, delay the removal of this ID.
            if allow_empty {
                return Ok(None);
            }
            return Err(Error::OutOfIdentifiers);
        }

        Ok(self
            .inner
            .iter()
            .position(|e| e.id() == id)
            .and_then(|index| self.inner.remove(index)))
    }
}

#[derive(Default)]
pub struct PathConnectionIdentifiers {
    /// The path ID space of the connection identifiers.
    path_id: PathId,

    /// All the Destination Connection IDs bound to the path provided by our
    /// peer.
    dcids: BoundedNonEmptyVecDeque<ConnectionIdEntry>,

    /// All the Source Connection IDs bound to the path we provide to our peer.
    scids: BoundedNonEmptyVecDeque<ConnectionIdEntry>,

    /// Retired Destination Connection IDs that should be announced to the peer.
    retire_dcid_seqs: BoundedConnectionIdSeqSet,

    /// Largest "Retire Prior To" we received from the peer.
    largest_peer_retire_prior_to: u64,

    /// Largest sequence number we received from the peer.
    largest_destination_seq: u64,

    /// Next sequence number to use.
    next_scid_seq: u64,

    /// "Retire Prior To" value to advertise to the peer.
    retire_prior_to: u64,

    /// The maximum number of source Connection IDs our peer allows us.
    source_conn_id_limit: usize,

    /// Are we in closing phase of the Path ID?
    closing: bool,

    /// Has initialized destination Connection ID?
    initialized_destination_connection_id: bool,

    /// Has initialized source Connection ID?
    initialized_source_connection_id: bool,
}

impl PathConnectionIdentifiers {
    /// Creates a new `PathConnectionIdentifiers` with the specified destination
    /// connection ID limit and initial source Connection ID. The initial
    /// destination connection ID is set to the empty one.
    fn new(
        destination_conn_id_limit: usize, source_conn_id_limit: usize,
        initial_scid: &ConnectionId, network_path: Option<FourTuple>,
        reset_token: Option<u128>,
    ) -> PathConnectionIdentifiers {
        let initial_scid =
            ConnectionId::from_ref(initial_scid.as_ref()).into_owned();

        Self::new_with_path_id(
            0,
            destination_conn_id_limit,
            source_conn_id_limit,
            Some(initial_scid),
            None,
            network_path,
            reset_token,
        )
    }

    fn new_with_path_id(
        path_id: PathId, mut destination_conn_id_limit: usize,
        mut source_conn_id_limit: usize,
        initial_scid: Option<ConnectionId<'static>>,
        initial_dcid: Option<ConnectionId<'static>>,
        network_path: Option<FourTuple>, reset_token: Option<u128>,
    ) -> PathConnectionIdentifiers {
        // It must be at least 2.
        if destination_conn_id_limit < 2 {
            destination_conn_id_limit = 2;
        }

        // Same for source conn id limit.
        if source_conn_id_limit < 2 {
            source_conn_id_limit = 2;
        }

        let initialized_destination_connection_id = initial_dcid.is_some();
        let initialized_source_connection_id = initial_scid.is_some();
        // Because we already inserted the initial SCID.
        let next_scid_seq = if initial_scid.is_some() { 1 } else { 0 };

        // Only one should be provided.
        assert!(
            initialized_destination_connection_id ^
                initialized_source_connection_id
        );

        let reset_token = initial_scid.as_ref().and(reset_token);
        // We need to track up to (2 * source_conn_id_limit - 1) source
        // Connection IDs when the host wants to force their renewal.
        let scids = BoundedNonEmptyVecDeque::new(
            2 * source_conn_id_limit - 1,
            ConnectionIdEntry {
                cid: initial_scid.unwrap_or_default(),
                seq: 0,
                reset_token,
                network_path,
            },
        );

        let reset_token = initial_dcid.as_ref().and(reset_token);
        let dcids = BoundedNonEmptyVecDeque::new(
            destination_conn_id_limit,
            ConnectionIdEntry {
                cid: initial_dcid.unwrap_or_default(),
                seq: 0,
                reset_token,
                network_path,
            },
        );

        PathConnectionIdentifiers {
            path_id,
            scids,
            dcids,
            retire_dcid_seqs: BoundedConnectionIdSeqSet::new(
                destination_conn_id_limit * RETIRED_CONN_ID_LIMIT_MULTIPLIER,
            ),
            next_scid_seq,
            source_conn_id_limit,
            initialized_destination_connection_id,
            initialized_source_connection_id,
            ..Default::default()
        }
    }

    /// Sets the maximum number of source connection IDs our peer allows us.
    fn set_source_conn_id_limit(&mut self, v: usize) {
        // Bound conn id limit so our scids queue sizing is valid.
        let v = std::cmp::min(v, usize::MAX / 2);

        // It must be at least 2.
        if v >= 2 {
            self.source_conn_id_limit = v;
            // We need to track up to (2 * source_conn_id_limit - 1) source
            // Connection IDs when the host wants to force their renewal.
            self.scids.resize(2 * v - 1);
        }
    }

    /// Gets the active destination Connection ID.
    fn get_dcid(&self, seq: CIDSeq) -> Option<&ConnectionIdEntry> {
        self.dcids.get(seq)
    }

    /// Gets the active source Connection ID.
    fn get_scid(&self, seq: CIDSeq) -> Option<&ConnectionIdEntry> {
        self.scids.get(seq)
    }

    /// Adds a new source identifier, and indicates whether it should be
    /// advertised through a `NEW_CONNECTION_ID` frame or not.
    ///
    /// At any time, the peer cannot have more Destination Connection IDs than
    /// the maximum number of active Connection IDs it negotiated. In such case
    /// (i.e., when [`active_source_cids()`] - `peer_active_conn_id_limit` = 0,
    /// if the caller agrees to request the removal of previous connection IDs,
    /// it sets the `retire_if_needed` parameter. Otherwise, an [`IdLimit`] is
    /// returned.
    ///
    /// Note that setting `retire_if_needed` does not prevent this function from
    /// returning an [`IdLimit`] in the case the caller wants to retire still
    /// unannounced Connection IDs.
    ///
    /// When setting the initial Source Connection ID, the `reset_token` may be
    /// `None`. However, other Source CIDs must have an associated
    /// `reset_token`. Providing `None` as the `reset_token` for non-initial
    /// SCIDs raises an [`InvalidState`].
    ///
    /// In the case the provided `cid` is already present, it does not add it.
    /// If the provided `reset_token` differs from the one already registered,
    /// returns an `InvalidState`.
    ///
    /// Returns whether a new entry has been added and the sequence number
    /// associated to that new source identifier.
    ///
    /// [`active_source_cids()`]:  struct.ConnectionIdentifiers.html#method.active_source_cids
    /// [`InvalidState`]: enum.Error.html#InvalidState
    /// [`IdLimit`]: enum.Error.html#IdLimit
    fn new_scid(
        &mut self, cid: ConnectionId<'static>, reset_token: Option<u128>,
        network_path: Option<FourTuple>, retire_if_needed: bool,
    ) -> Result<(bool, u64)> {
        if !self.initialized_source_connection_id {
            self.set_initial_scid(cid, reset_token, network_path);
            return Ok((true, 0));
        }

        // Check whether the number of source Connection IDs does not exceed the
        // limit. If the host agrees to retire old CIDs, it can store up to
        // (2 * source_active_conn_id - 1) source CIDs. This limit is enforced
        // when calling `self.scids.insert()`.
        if self.scids.len() >= self.source_conn_id_limit {
            if !retire_if_needed {
                return Err(Error::IdLimit);
            }

            // We need to retire the lowest one.
            self.retire_prior_to = self.lowest_usable_scid_seq()? + 1;
        }

        let seq = self.next_scid_seq;

        if reset_token.is_none() && seq != 0 {
            return Err(Error::InvalidState);
        }

        // Check first that the SCID has not been inserted before.
        if let Some(e) = self.scids.iter().find(|e| e.cid == cid) {
            if e.reset_token != reset_token {
                return Err(Error::InvalidState);
            }
            return Ok((false, e.seq));
        }

        // Is this the first SCID?

        self.scids.insert(ConnectionIdEntry {
            cid,
            seq,
            reset_token,
            network_path,
        })?;
        self.next_scid_seq += 1;

        Ok((true, seq))
    }

    /// Gets the minimum Source Connection ID sequence number whose removal has
    /// not been requested yet.
    #[inline]
    fn lowest_usable_scid_seq(&self) -> Result<CIDSeq> {
        self.scids
            .iter()
            .filter_map(|e| {
                if e.seq >= self.retire_prior_to {
                    Some(e.seq)
                } else {
                    None
                }
            })
            .min()
            .ok_or(Error::InvalidState)
    }

    /// Sets the initial destination identifier.
    fn set_initial_dcid(
        &mut self, cid: ConnectionId<'static>, seq: CIDSeq,
        reset_token: Option<u128>, network_path: Option<FourTuple>,
    ) {
        self.dcids.clear_and_insert(ConnectionIdEntry {
            cid,
            seq,
            reset_token,
            network_path,
        });
        self.initialized_destination_connection_id = true;
    }

    /// Sets the initial source identifier.
    fn set_initial_scid(
        &mut self, cid: ConnectionId<'static>, reset_token: Option<u128>,
        network_path: Option<FourTuple>,
    ) {
        self.scids.clear_and_insert(ConnectionIdEntry {
            cid,
            seq: 0,
            reset_token,
            network_path,
        });
        self.initialized_source_connection_id = true;
    }

    fn next_scid_seq(&self) -> CIDSeq {
        self.next_scid_seq
    }

    /// Adds a new Destination Connection ID (originating from a
    /// NEW_CONNECTION_ID frame) and process all its related metadata.
    ///
    /// Returns an error if the provided Connection ID or its metadata are
    /// invalid.
    ///
    /// Returns a list of DCID sequence numbers, containing the
    /// sequence number of retired DCIDs on the given PathId.
    fn new_dcid(
        &mut self, cid: ConnectionId<'static>, seq: CIDSeq, reset_token: u128,
        retire_prior_to: CIDSeq,
        retired_path_ids: &mut SmallVec<[(u64, FourTuple); 1]>,
    ) -> Result<()> {
        // If it is the first DCID seen, insert and return.
        if !self.initialized_destination_connection_id {
            self.set_initial_dcid(cid, seq, Some(reset_token), None);
            return Ok(());
        }

        // If an endpoint receives a NEW_CONNECTION_ID frame that repeats a
        // previously issued connection ID with a different Stateless Reset
        // Token field value or a different Sequence Number field value, or if a
        // sequence number is used for different connection IDs, the endpoint
        // MAY treat that receipt as a connection error of type
        // PROTOCOL_VIOLATION.
        if let Some(e) = self.dcids.iter().find(|e| e.cid == cid || e.seq == seq)
        {
            if e.cid != cid || e.seq != seq || e.reset_token != Some(reset_token)
            {
                return Err(Error::InvalidFrame);
            }
            // The identifier is already there, nothing to do.
            return Ok(());
        }

        // The value in the Retire Prior To field MUST be less than or equal to
        // the value in the Sequence Number field. Receiving a value in the
        // Retire Prior To field that is greater than that in the Sequence
        // Number field MUST be treated as a connection error of type
        // FRAME_ENCODING_ERROR.
        if retire_prior_to > seq {
            return Err(Error::InvalidFrame);
        }

        // An endpoint that receives a NEW_CONNECTION_ID frame with a sequence
        // number smaller than the Retire Prior To field of a previously
        // received NEW_CONNECTION_ID frame MUST send a corresponding
        // RETIRE_CONNECTION_ID frame that retires the newly received connection
        // ID, unless it has already done so for that sequence number.
        if seq < self.largest_peer_retire_prior_to {
            self.mark_retire_dcid_seq(seq, true)?;
            return Ok(());
        }

        if seq > self.largest_destination_seq {
            self.largest_destination_seq = seq;
        }

        let new_entry = ConnectionIdEntry {
            cid: cid.clone(),
            seq,
            reset_token: Some(reset_token),
            network_path: None,
        };

        let mut retired_dcid_queue_err = None;

        // A receiver MUST ignore any Retire Prior To fields that do not
        // increase the largest received Retire Prior To value.
        //
        // After processing a NEW_CONNECTION_ID frame and adding and retiring
        // active connection IDs, if the number of active connection IDs exceeds
        // the value advertised in its active_connection_id_limit transport
        // parameter, an endpoint MUST close the connection with an error of type
        // CONNECTION_ID_LIMIT_ERROR.
        if retire_prior_to > self.largest_peer_retire_prior_to {
            let retired = &mut self.retire_dcid_seqs;

            // The insert entry MUST have a sequence higher or equal to the ones
            // being retired.
            if new_entry.seq < retire_prior_to {
                return Err(Error::OutOfIdentifiers);
            }

            // To avoid exceeding the capacity of the inner `VecDeque`, we first
            // remove the elements and then insert the new one.
            let index = self
                .dcids
                .inner
                .partition_point(|e| e.seq < retire_prior_to);

            for e in self.dcids.inner.drain(..index) {
                if let Some(nw) = e.network_path {
                    retired_path_ids.push((e.seq, nw));
                }

                if let Err(e) = retired.insert(e.seq) {
                    // Delay propagating the error as we need to try to insert
                    // the new DCID first.
                    retired_dcid_queue_err = Some(e);
                    break;
                }
            }

            self.largest_peer_retire_prior_to = retire_prior_to;
        }

        // Note that if no element has been retired and the `VecDeque` reaches
        // its capacity limit, this will raise an `IdLimit`.
        self.dcids.insert(new_entry)?;

        // Propagate the error triggered when inserting a retired DCID seq to
        // the queue.
        if let Some(e) = retired_dcid_queue_err {
            return Err(e);
        }

        Ok(())
    }

    /// Retires the Source Connection ID having the provided sequence number.
    ///
    /// In case the retired Connection ID is the same as the one used by the
    /// packet requesting the retiring, or if the retired sequence number is
    /// greater than any previously advertised sequence numbers, it returns an
    /// [`InvalidState`].
    ///
    /// Returns the retired source Connection Id entry, if any.
    ///
    /// [`InvalidState`]: enum.Error.html#InvalidState
    fn retire_scid(
        &mut self, seq: CIDSeq, pkt_dcid: &ConnectionId,
    ) -> Result<Option<ConnectionIdEntry>> {
        if seq >= self.next_scid_seq {
            return Err(Error::InvalidState);
        }

        let entry = if let Some(e) = self.scids.remove(seq, self.closing)? {
            if e.cid == *pkt_dcid {
                return Err(Error::InvalidState);
            }

            // Retiring this SCID may increase the retire prior to.
            let lowest_scid_seq = self.lowest_usable_scid_seq()?;
            self.retire_prior_to = lowest_scid_seq;

            Some(e)
        } else {
            None
        };

        Ok(entry)
    }

    /// Retires the Destination Connection ID having the provided sequence
    /// number.
    ///
    /// If the caller tries to retire the last destination Connection ID, this
    /// method triggers an [`OutOfIdentifiers`].
    ///
    /// If the caller tries to retire a non-existing Destination Connection
    /// ID sequence number, this method returns an [`InvalidState`].
    ///
    /// Returns the four-tuple that was associated to the retired CID, if any.
    ///
    /// [`OutOfIdentifiers`]: enum.Error.html#OutOfIdentifiers
    /// [`InvalidState`]: enum.Error.html#InvalidState
    pub fn retire_dcid(&mut self, seq: CIDSeq) -> Result<Option<FourTuple>> {
        match self.dcids.remove(seq, self.closing)? {
            Some(e) => {
                self.mark_retire_dcid_seq(seq, true)?;
                Ok(e.network_path)
            },
            None if self.closing => Ok(None),
            None => Err(Error::InvalidState),
        }
    }

    /// Gets the lowest Destination Connection ID sequence number that is not
    /// associated to a path.
    #[inline]
    fn lowest_available_dcid_seq(&self) -> Option<u64> {
        self.dcids
            .iter()
            .filter_map(|e| {
                if e.network_path.is_none() {
                    Some(e.seq)
                } else {
                    None
                }
            })
            .min()
    }

    /// Adds or remove the destination Connection ID sequence number from the
    /// retired destination Connection ID set that need to be advertised to the
    /// peer through RETIRE_CONNECTION_ID frames.
    #[inline]
    pub fn mark_retire_dcid_seq(
        &mut self, dcid_seq: u64, retire: bool,
    ) -> Result<()> {
        if retire {
            self.retire_dcid_seqs.insert(dcid_seq)?;
        } else {
            self.retire_dcid_seqs.remove(&dcid_seq);
        }

        Ok(())
    }
}

impl Identifiable for PathConnectionIdentifiers {
    fn id(&self) -> u64 {
        self.path_id
    }
}

/// An iterator over QUIC streams.
#[derive(Default)]
pub struct PathIdIter {
    path_ids: SmallVec<[u64; 8]>,
    index: usize,
}

impl PathIdIter {
    #[inline]
    fn from(max_path_id: PathId, exclude: &[PathId]) -> Self {
        PathIdIter {
            path_ids: (0..=max_path_id)
                .filter(|p| !exclude.contains(p))
                .collect(),
            index: 0,
        }
    }
}

impl Iterator for PathIdIter {
    type Item = u64;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let v = self.path_ids.get(self.index)?;
        self.index += 1;
        Some(*v)
    }
}

impl ExactSizeIterator for PathIdIter {
    #[inline]
    fn len(&self) -> usize {
        self.path_ids.len() - self.index
    }
}

#[derive(Default)]
pub struct ConnectionIdentifiers {
    /// All the Destination Connection IDs provided by our peer.
    pcids: BoundedNonEmptyVecDeque<PathConnectionIdentifiers>,

    /// Source Connection IDs that should be announced to the peer.
    advertise_new_scid_seqs: VecDeque<(PathId, CIDSeq)>,

    /// Retired Source Connection IDs that should be notified to the
    /// application.
    retired_scids: VecDeque<(PathId, ConnectionId<'static>)>,

    /// The maximum number of source Connection IDs our peer allows us.
    source_conn_id_limit: usize,

    /// The maximum number of destination Connection IDs we allow.
    destination_conn_id_limit: usize,

    /// Closed path Ids.
    closed_path_id: Vec<PathId>,

    /// Available path IDs to use -- for client use only!!!
    spare_path_ids: BinaryHeap<Reverse<PathId>>,

    /// Maximum path ID that we allow on this connection.
    local_max_path_id: PathId,

    /// Maximum path ID that our peer allows on this connection.
    remote_max_path_id: PathId,

    /// Largest path ID seen on this connection.
    largest_path_id: PathId,

    /// Whether we should advertise the local max path id.
    advertise_local_max_path_id: bool,

    /// Does the host use zero-length source Connection ID.
    zero_length_scid: bool,

    /// Does the host use zero-length destination Connection ID.
    zero_length_dcid: bool,
}

impl ConnectionIdentifiers {
    /// Creates a new `ConnectionIdentifiers` with the specified destination
    /// connection ID limit and initial source Connection ID. The destination
    /// Connection ID is set to the empty one.
    pub fn new(
        mut destination_conn_id_limit: usize, initial_scid: &ConnectionId,
        network_path: FourTuple, reset_token: Option<u128>,
    ) -> ConnectionIdentifiers {
        // It must be at least 2.
        if destination_conn_id_limit < 2 {
            destination_conn_id_limit = 2;
        }

        // Initially, the limit of active source connection IDs is 2.
        let source_conn_id_limit = 2;

        // Record the zero-length SCID status.
        let zero_length_scid = initial_scid.is_empty();

        // TODO: we may limit the capacity of the range set up to the number of
        // active paths a host is willing to hold.

        let pcids = BoundedNonEmptyVecDeque::new(
            1, /* most connections only have a single PathId, only multipath
                * ones have more. */
            PathConnectionIdentifiers::new(
                destination_conn_id_limit,
                source_conn_id_limit,
                initial_scid,
                Some(network_path),
                reset_token,
            ),
        );

        ConnectionIdentifiers {
            pcids,
            retired_scids: VecDeque::new(),
            destination_conn_id_limit,
            source_conn_id_limit,
            zero_length_scid,
            ..Default::default()
        }
    }

    #[inline]
    fn get_pcids(&self, path_id: PathId) -> Option<&PathConnectionIdentifiers> {
        self.pcids.iter().find(|pcid| pcid.path_id == path_id)
    }

    #[inline]
    fn get_pcids_mut(
        &mut self, path_id: PathId,
    ) -> Option<&mut PathConnectionIdentifiers> {
        self.pcids
            .iter_mut()
            .find_map(|pcid| (pcid.path_id == path_id).then_some(pcid))
    }

    /// Sets the maximum number of source connection IDs our peer allows us.
    pub fn set_source_conn_id_limit(&mut self, v: u64) {
        // Bound conn id limit so our scids queue sizing is valid.
        let v = std::cmp::min(v, (usize::MAX / 2) as u64) as usize;

        // It must be at least 2.
        if v >= 2 {
            self.source_conn_id_limit = v;
            self.pcids
                .iter_mut()
                .for_each(|pcid| pcid.set_source_conn_id_limit(v));
        }
    }

    /// When the max path ID change.
    fn maybe_resize_pcids(&mut self) {
        // Assumption: only client-initiated paths.
        self.pcids.resize((1 + self.max_path_id()) as usize);
    }

    /// Sets the maximum path ID we allow, and specify if we should advertise
    /// this new value.
    pub fn set_local_max_path_id(&mut self, v: PathId, advertise: bool) {
        if v > self.local_max_path_id {
            self.local_max_path_id = v;
            if advertise {
                self.advertise_local_max_path_id = true;
            }
            self.maybe_resize_pcids();
        }
    }

    /// Sets the maximum path ID our peer allows.
    pub fn set_remote_max_path_id(&mut self, v: PathId) {
        if v > self.remote_max_path_id {
            self.remote_max_path_id = v;
            self.maybe_resize_pcids();
        }
    }

    /// Do we have some spare Path Id?
    pub fn has_spare_path_id(&self) -> bool {
        self.spare_path_ids.peek().is_some()
    }

    /// Returns the lowest unused client-side Path Id.
    pub fn lowest_spare_path_id(&self) -> Option<PathId> {
        self.spare_path_ids.peek().map(|r| r.0)
    }

    /// Indicates that we consume the lowest unused client-side Path Id.
    pub fn consume_lowest_spare_path_id(&mut self) {
        self.spare_path_ids.pop();
    }

    /// Gets the active destination Connection ID associated with the path ID.
    #[inline]
    pub fn get_dcid(
        &self, path_id: PathId, seq_num: CIDSeq,
    ) -> Result<&ConnectionIdEntry> {
        self.get_pcids(path_id)
            .and_then(|pcid| pcid.get_dcid(seq_num))
            .ok_or(Error::InvalidState)
    }

    /// Gets the source Connection ID associated with the provided sequence
    /// number.
    #[inline]
    pub fn get_scid(
        &self, path_id: PathId, seq_num: CIDSeq,
    ) -> Result<&ConnectionIdEntry> {
        self.get_pcids(path_id)
            .and_then(|pcid| pcid.get_scid(seq_num))
            .ok_or(Error::InvalidState)
    }

    /// Adds a new source identifier, and indicates whether it should be
    /// advertised through a `NEW_CONNECTION_ID` frame or not.
    ///
    /// At any time, the peer cannot have more Destination Connection IDs than
    /// the maximum number of active Connection IDs it negotiated. In such case
    /// (i.e., when [`active_source_cids()`] - `peer_active_conn_id_limit` = 0,
    /// if the caller agrees to request the removal of previous connection IDs,
    /// it sets the `retire_if_needed` parameter. Otherwise, an [`IdLimit`] is
    /// returned.
    ///
    /// Note that setting `retire_if_needed` does not prevent this function from
    /// returning an [`IdLimit`] in the case the caller wants to retire still
    /// unannounced Connection IDs.
    ///
    /// When setting the initial Source Connection ID, the `reset_token` may be
    /// `None`. However, other Source CIDs must have an associated
    /// `reset_token`. Providing `None` as the `reset_token` for non-initial
    /// SCIDs raises an [`InvalidState`].
    ///
    /// In the case the provided `cid` is already present, it does not add it.
    /// If the provided `reset_token` differs from the one already registered,
    /// returns an `InvalidState`.
    ///
    /// Returns the sequence number associated to that new source identifier.
    ///
    /// [`active_source_cids()`]:  struct.ConnectionIdentifiers.html#method.active_source_cids
    /// [`InvalidState`]: enum.Error.html#InvalidState
    /// [`IdLimit`]: enum.Error.html#IdLimit
    pub fn new_scid(
        &mut self, path_id: PathId, cid: ConnectionId<'static>,
        reset_token: Option<u128>, advertise: bool,
        network_path: Option<FourTuple>, retire_if_needed: bool,
    ) -> Result<u64> {
        if self.zero_length_scid {
            return Err(Error::InvalidState);
        }

        if reset_token.is_none() && path_id != 0 {
            return Err(Error::InvalidState);
        }

        // We may create a new path-specific space.
        let (inserted, seq) = match self.get_pcids_mut(path_id) {
            Some(p) =>
                p.new_scid(cid, reset_token, network_path, retire_if_needed)?,
            None => {
                // Are we requesting some valid max path?
                if path_id > self.max_path_id() {
                    return Err(Error::OutOfPathId);
                }

                // Or was it closed?
                if self.closed_path_id.contains(&path_id) {
                    return Err(Error::OutOfPathId);
                }

                // Try to insert a new PathConnectionID then.
                self.pcids.insert(
                    PathConnectionIdentifiers::new_with_path_id(
                        path_id,
                        self.destination_conn_id_limit,
                        self.source_conn_id_limit,
                        Some(cid),
                        None,
                        network_path,
                        reset_token,
                    ),
                )?;
                self.spare_path_ids.push(Reverse(path_id));
                self.largest_path_id = self.largest_path_id.max(path_id);
                (true, 0)
            },
        };
        if inserted {
            self.mark_advertise_new_scid_seq(path_id, seq, advertise);
        }

        Ok(seq)
    }

    /// Sets the initial destination identifier.
    pub fn set_initial_dcid(
        &mut self, cid: ConnectionId<'static>, reset_token: Option<u128>,
        network_path: Option<FourTuple>,
    ) {
        // Record the zero-length DCID status.
        self.zero_length_dcid = cid.is_empty();
        if let Some(pcid) = self.get_pcids_mut(0) {
            pcid.set_initial_dcid(cid, 0, reset_token, network_path);
        }
    }

    /// Adds a new Destination Connection ID (originating from a
    /// NEW_CONNECTION_ID frame) and process all its related metadata.
    ///
    /// Returns an error if the provided Connection ID or its metadata are
    /// invalid.
    ///
    /// Returns a list of DCID sequence numbers, containing the
    /// sequence number of retired DCIDs on the given PathId.
    pub fn new_dcid(
        &mut self, path_id: PathId, cid: ConnectionId<'static>, seq: u64,
        reset_token: u128, retire_prior_to: u64,
        retired_path_ids: &mut SmallVec<[(u64, FourTuple); 1]>,
    ) -> Result<()> {
        if self.zero_length_dcid {
            return Err(Error::InvalidState);
        }

        match self.get_pcids_mut(path_id) {
            Some(p) => p.new_dcid(
                cid,
                seq,
                reset_token,
                retire_prior_to,
                retired_path_ids,
            ),
            None => {
                // Are we requesting some valid max path?
                if path_id > self.max_path_id() {
                    return Err(Error::OutOfPathId);
                }

                // Or was it closed?
                if self.closed_path_id.contains(&path_id) {
                    return Err(Error::OutOfPathId);
                }

                // Try to insert a new PathConnectionID then.
                self.pcids.insert(
                    PathConnectionIdentifiers::new_with_path_id(
                        path_id,
                        self.destination_conn_id_limit,
                        self.source_conn_id_limit,
                        None,
                        Some(cid),
                        None,
                        Some(reset_token),
                    ),
                )?;

                if path_id % 2 == 0 {
                    self.spare_path_ids.push(Reverse(path_id));
                }
                self.largest_path_id = self.largest_path_id.max(path_id);

                Ok(())
            },
        }
    }

    /// Retires the Source Connection ID having the provided sequence number.
    ///
    /// In case the retired Connection ID is the same as the one used by the
    /// packet requesting the retiring, or if the retired sequence number is
    /// greater than any previously advertised sequence numbers, it returns an
    /// [`InvalidState`].
    ///
    /// Returns the four-tuple that was associated to the retired CID, if any.
    ///
    /// [`InvalidState`]: enum.Error.html#InvalidState
    pub fn retire_scid(
        &mut self, path_id: PathId, seq: CIDSeq, pkt_dcid: &ConnectionId,
    ) -> Result<Option<FourTuple>> {
        // If the path ID does not exist anymore, ignore the request.
        let pcid = match self.get_pcids_mut(path_id) {
            Some(p) => p,
            None => return Ok(None),
        };

        match pcid.retire_scid(seq, pkt_dcid)? {
            Some(e) => {
                // Notifies the application.
                self.retired_scids.push_back((path_id, e.cid));
                Ok(e.network_path)
            },
            None => Ok(None),
        }
    }

    /// Retires the Destination Connection ID having the provided sequence
    /// number.
    ///
    /// If the caller tries to retire the last destination Connection ID, this
    /// method triggers an [`OutOfIdentifiers`].
    ///
    /// If the caller tries to retire a non-existing Destination Connection
    /// ID sequence number, this method returns an [`InvalidState`].
    ///
    /// Returns the four-tuple that was associated to the retired CID, if any.
    ///
    /// [`OutOfIdentifiers`]: enum.Error.html#OutOfIdentifiers
    /// [`InvalidState`]: enum.Error.html#InvalidState
    pub fn retire_dcid(
        &mut self, path_id: PathId, seq: CIDSeq,
    ) -> Result<Option<FourTuple>> {
        if self.zero_length_dcid {
            return Err(Error::InvalidState);
        }
        // If we later receive a retire DCID for a closed path ID, ignore.
        if self.closed_path_id.contains(&path_id) {
            return Ok(None);
        }
        self.get_pcids_mut(path_id)
            .ok_or(Error::OutOfPathId)
            .and_then(|pcid| pcid.retire_dcid(seq))
    }

    /// Returns an iterator over the source connection IDs.
    pub fn scids_iter(&self) -> impl Iterator<Item = &ConnectionId> {
        self.pcids
            .iter()
            .flat_map(|pcid| pcid.scids.iter().map(|e| &e.cid))
    }

    /// Updates the Source Connection ID entry with the provided sequence number
    /// to indicate that it is now linked to the provided path ID.
    pub fn link_scid_to_network_path(
        &mut self, path_id: PathId, scid_seq: CIDSeq, network_path: FourTuple,
    ) -> Result<()> {
        let e = self
            .get_pcids_mut(path_id)
            .ok_or(Error::OutOfPathId)
            .and_then(|pcid| {
                pcid.scids.get_mut(scid_seq).ok_or(Error::InvalidState)
            })?;
        e.network_path = Some(network_path);
        Ok(())
    }

    /// Updates the Destination Connection ID entry with the provided sequence
    /// number to indicate that it is now linked to the provided path ID.
    pub fn link_dcid_to_network_path(
        &mut self, path_id: PathId, dcid_seq: CIDSeq, network_path: FourTuple,
    ) -> Result<()> {
        let e = self
            .get_pcids_mut(path_id)
            .ok_or(Error::OutOfPathId)
            .and_then(|pcid| {
                pcid.dcids.get_mut(dcid_seq).ok_or(Error::InvalidState)
            })?;
        e.network_path = Some(network_path);
        Ok(())
    }

    /// Gets the lowest Destination Connection ID sequence number that is not
    /// associated to a path.
    #[inline]
    pub fn lowest_available_dcid_seq(&self, path_id: PathId) -> Option<u64> {
        self.get_pcids(path_id)
            .and_then(|pcid| pcid.lowest_available_dcid_seq())
    }

    /// Finds the path ID and the sequence number of the Source Connection ID
    /// having the provided value and the network path using it, if any.
    #[inline]
    pub fn find_scid_path_id_and_seq(
        &self, scid: &ConnectionId,
    ) -> Option<(PathId, CIDSeq, Option<FourTuple>)> {
        self.pcids.iter().find_map(|pcid| {
            pcid.scids.iter().find_map(|e| {
                if e.cid == *scid {
                    Some((pcid.path_id, e.seq, e.network_path))
                } else {
                    None
                }
            })
        })
    }

    /// Returns the number of Source Connection IDs that have not been
    /// assigned to a path yet.
    ///
    /// Note that this function is only meaningful if the host uses non-zero
    /// length Source Connection IDs.
    #[inline]
    pub fn available_scids(&self) -> usize {
        self.available_scids_on_path(0)
    }

    /// Returns the number of Source Connection IDs that have not been
    /// assigned to a path yet.
    ///
    /// Note that this function is only meaningful if the host uses non-zero
    /// length Source Connection IDs.
    #[inline]
    pub fn available_scids_on_path(&self, path_id: PathId) -> usize {
        self.get_pcids(path_id)
            .map(|pcid| {
                pcid.scids
                    .iter()
                    .filter(|e| e.network_path.is_none())
                    .count()
            })
            .unwrap_or(0)
    }

    /// Returns the number of Destination Connection IDs that have not been
    /// assigned to a path yet.
    ///
    /// Note that this function returns 0 if the host uses zero length
    /// Destination Connection IDs.
    #[inline]
    pub fn available_dcids(&self) -> usize {
        self.available_dcids_on_path(0)
    }

    /// Returns the number of Destination Connection IDs bound to the given
    /// PathId that have not been assigned yet on a network path.
    ///
    /// Note that this function returns 0 if the host uses zero length
    /// Destination Connection IDs.
    #[inline]
    pub fn available_dcids_on_path(&self, path_id: PathId) -> usize {
        if self.zero_length_dcid() {
            return 0;
        }
        self.get_pcids(path_id)
            .map(|pcid| {
                pcid.dcids
                    .iter()
                    .filter(|e| e.network_path.is_none())
                    .count()
            })
            .unwrap_or(0)
    }

    /// Returns the oldest active source Connection ID of this connection.
    #[inline]
    pub fn oldest_scid(&self) -> &ConnectionIdEntry {
        self.pcids.get_oldest().scids.get_oldest()
    }

    /// Returns the oldest active source Connection ID on a given path ID.
    #[inline]
    pub fn oldest_scid_on_path(
        &self, path_id: PathId,
    ) -> Option<&ConnectionIdEntry> {
        self.get_pcids(path_id).map(|pcid| pcid.scids.get_oldest())
    }

    /// Returns the oldest active destination Connection ID on a given path ID.
    #[inline]
    pub fn oldest_dcid_on_path(
        &self, path_id: PathId,
    ) -> Option<&ConnectionIdEntry> {
        self.get_pcids(path_id).map(|pcid| pcid.dcids.get_oldest())
    }

    /// Returns the oldest known active destination Connection ID of this
    /// connection.
    ///
    /// Note that due to e.g., reordering at reception side, the oldest known
    /// active destination Connection ID is not necessarily the one having the
    /// lowest sequence.
    #[inline]
    pub fn oldest_dcid(&self) -> &ConnectionIdEntry {
        self.pcids.get_oldest().dcids.get_oldest()
    }

    /// Adds or remove the source Connection ID sequence number from the
    /// source Connection ID set that need to be advertised to the peer through
    /// NEW_CONNECTION_ID frames.
    #[inline]
    pub fn mark_advertise_new_scid_seq(
        &mut self, path_id: PathId, scid_seq: CIDSeq, advertise: bool,
    ) {
        if advertise {
            if !self.advertise_new_scid_seqs.contains(&(path_id, scid_seq)) {
                self.advertise_new_scid_seqs.push_back((path_id, scid_seq));
            }
        } else if let Some(index) = self
            .advertise_new_scid_seqs
            .iter()
            .position(|s| *s == (path_id, scid_seq))
        {
            self.advertise_new_scid_seqs.remove(index);
        }
    }

    /// Adds or remove the destination Connection ID sequence number from the
    /// retired destination Connection ID set that need to be advertised to the
    /// peer through RETIRE_CONNECTION_ID frames.
    #[inline]
    pub fn mark_retire_dcid_seq(
        &mut self, path_id: PathId, dcid_seq: CIDSeq, retire: bool,
    ) -> Result<()> {
        self.get_pcids_mut(path_id)
            .ok_or(Error::UnavailablePath)?
            .mark_retire_dcid_seq(dcid_seq, retire)
    }

    /// Gets a source Connection ID's sequence number requiring advertising it
    /// to the peer through NEW_CONNECTION_ID frame, if any.
    ///
    /// If `Some`, it always returns the same value until it has been removed
    /// using `mark_advertise_new_scid_seq`.
    #[inline]
    pub fn next_advertise_new_scid_seq(&self) -> Option<(PathId, CIDSeq)> {
        self.advertise_new_scid_seqs.front().copied()
    }

    /// Gets a destination Connection IDs's sequence number that need to send
    /// RETIRE_CONNECTION_ID frames.
    ///
    /// If `Some`, it always returns the same value until it has been removed
    /// using `mark_retire_dcid_seq`.
    #[inline]
    pub fn next_retire_dcid_seq(&self) -> Option<(PathId, CIDSeq)> {
        self.pcids.iter().find_map(|pcid| {
            pcid.retire_dcid_seqs.front().map(|c| (pcid.path_id, c))
        })
    }

    /// Returns true if there are new source Connection IDs to advertise.
    #[inline]
    pub fn has_new_scids(&self) -> bool {
        !self.advertise_new_scid_seqs.is_empty()
    }

    /// Returns true if there are retired destination Connection IDs to\
    /// advertise.
    #[inline]
    pub fn has_retire_dcids(&self) -> bool {
        self.pcids.iter().any(|p| !p.retire_dcid_seqs.is_empty())
    }

    /// Returns whether zero-length source CIDs are used.
    #[inline]
    pub fn zero_length_scid(&self) -> bool {
        self.zero_length_scid
    }

    /// Returns whether zero-length destination CIDs are used.
    #[inline]
    pub fn zero_length_dcid(&self) -> bool {
        self.zero_length_dcid
    }

    /// Gets the (PATH_)NEW_CONNECTION_ID frame related to the source connection
    /// ID with path ID `path_id` and sequence `seq_num`.
    pub fn get_path_connection_id_frame_for(
        &self, path_id: PathId, seq_num: CIDSeq,
    ) -> Result<frame::Frame> {
        let pcid = self.get_pcids(path_id).ok_or(Error::OutOfPathId)?;
        let e = pcid.scids.get(seq_num).ok_or(Error::InvalidState)?;
        if path_id != 0 {
            Ok(frame::Frame::PathNewConnectionId {
                path_id,
                seq_num,
                retire_prior_to: pcid.retire_prior_to,
                conn_id: e.cid.to_vec(),
                reset_token: e
                    .reset_token
                    .ok_or(Error::InvalidState)?
                    .to_be_bytes(),
            })
        } else {
            Ok(frame::Frame::NewConnectionId {
                seq_num,
                retire_prior_to: pcid.retire_prior_to,
                conn_id: e.cid.to_vec(),
                reset_token: e
                    .reset_token
                    .ok_or(Error::InvalidState)?
                    .to_be_bytes(),
            })
        }
    }

    /// Returns the number of source Connection IDs on a given path ID that are
    /// active. This is only meaningful if the host uses non-zero length
    /// Source Connection IDs.
    #[inline]
    pub fn active_source_cids_on_path(&self, path_id: PathId) -> usize {
        self.get_pcids(path_id)
            .map(|pcid| pcid.scids.len())
            .unwrap_or(0)
    }

    /// Returns the number of source Connection IDs that are active. This is
    /// only meaningful if the host uses non-zero length Source Connection IDs.
    #[inline]
    pub fn active_source_cids(&self) -> usize {
        self.pcids.iter().map(|pcid| pcid.scids.len()).sum()
    }

    /// Returns the number of source Connection IDs that are retired. This is
    /// only meaningful if the host uses non-zero length Source Connection IDs.
    #[inline]
    pub fn retired_source_cids(&self) -> usize {
        self.retired_scids.len()
    }

    pub fn pop_retired_scid(
        &mut self,
    ) -> Option<(PathId, ConnectionId<'static>)> {
        self.retired_scids.pop_front()
    }

    /// Returns the max path ID authorized on this connection.
    #[inline]
    pub fn max_path_id(&self) -> PathId {
        self.local_max_path_id.min(self.remote_max_path_id)
    }

    /// Returns the local max path ID we allow on this connection.
    #[inline]
    pub fn local_max_paths_id(&self) -> PathId {
        self.local_max_path_id
    }

    /// Whether we should send a MAX_PATHS frame.
    #[inline]
    pub fn should_send_max_paths(&self) -> bool {
        self.advertise_local_max_path_id
    }

    /// When a MAX_PATHS frame has been sent.
    #[inline]
    pub fn on_max_path_id_sent(&mut self) {
        self.advertise_local_max_path_id = false;
    }

    /// Returns the largest path ID number seen.
    #[inline]
    pub fn largest_path_id(&self) -> PathId {
        self.largest_path_id
    }

    pub fn closing_path_id(&mut self, path_id: PathId) {
        if let Some(pcid) = self.get_pcids_mut(path_id) {
            pcid.closing = true;
        }
    }

    /// Remove a path identifier from the Connection IDs.
    pub fn remove_path_id(&mut self, path_id: PathId) -> Result<()> {
        if self.closed_path_id.contains(&path_id) {
            warn!(
                "retiring CIDs of an already closed path id {}; ignoring",
                path_id
            );
            return Ok(());
        }
        if path_id > self.max_path_id() {
            return Err(Error::PathIdViolation);
        }
        // We may close a path ID for which we have no state.
        if let Some(mut pcid) = self.pcids.remove(path_id, false)? {
            // May not be needed with latest draft version.
            for e in pcid
                .dcids
                .inner
                .drain(..)
                .collect::<Vec<ConnectionIdEntry>>()
            {
                pcid.mark_retire_dcid_seq(e.seq, true)?;
            }
            for e in pcid.scids.inner.drain(..) {
                self.retired_scids.push_back((path_id, e.cid));
            }
        };
        // Record that the path ID was closed.
        self.closed_path_id.push(path_id);
        Ok(())
    }

    /// An iterator over valid path IDs.
    pub fn path_ids(&self) -> PathIdIter {
        PathIdIter::from(self.max_path_id(), &self.closed_path_id)
    }

    /// Helper function for tests.
    #[allow(dead_code)]
    pub fn next_scid_seq_on_path_id(&self, path_id: PathId) -> CIDSeq {
        self.get_pcids(path_id)
            .map(|p| p.next_scid_seq())
            .unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::create_cid_and_reset_token;

    #[test]
    fn ids_new_scids() {
        let (scid, _) = create_cid_and_reset_token(16);
        let (dcid, _) = create_cid_and_reset_token(16);
        let network_path: FourTuple = (
            "1.2.3.4:8000".parse().unwrap(),
            "5.6.7.8:8008".parse().unwrap(),
        );

        let mut ids = ConnectionIdentifiers::new(2, &scid, network_path, None);
        ids.set_source_conn_id_limit(3);
        ids.set_initial_dcid(dcid, None, Some(network_path));

        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.available_scids(), 0);
        assert!(!ids.has_new_scids());
        assert_eq!(ids.next_advertise_new_scid_seq(), None);

        let (scid2, rt2) = create_cid_and_reset_token(16);

        assert_eq!(ids.new_scid(0, scid2, Some(rt2), true, None, false), Ok(1));
        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.available_scids(), 1);
        assert!(ids.has_new_scids());
        assert_eq!(ids.next_advertise_new_scid_seq(), Some((0, 1)));

        let (scid3, rt3) = create_cid_and_reset_token(16);

        assert_eq!(ids.new_scid(0, scid3, Some(rt3), true, None, false), Ok(2));
        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.available_scids(), 2);
        assert!(ids.has_new_scids());
        assert_eq!(ids.next_advertise_new_scid_seq(), Some((0, 1)));

        // If now we give another CID, it reports an error since it exceeds the
        // limit of active CIDs.
        let (scid4, rt4) = create_cid_and_reset_token(16);

        assert_eq!(
            ids.new_scid(0, scid4, Some(rt4), true, None, false),
            Err(Error::IdLimit),
        );
        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.available_scids(), 2);
        assert!(ids.has_new_scids());
        assert_eq!(ids.next_advertise_new_scid_seq(), Some((0, 1)));

        // Assume we sent one of them.
        ids.mark_advertise_new_scid_seq(0, 1, false);
        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.available_scids(), 2);
        assert!(ids.has_new_scids());
        assert_eq!(ids.next_advertise_new_scid_seq(), Some((0, 2)));

        // Send the other.
        ids.mark_advertise_new_scid_seq(0, 2, false);

        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.available_scids(), 2);
        assert!(!ids.has_new_scids());
        assert_eq!(ids.next_advertise_new_scid_seq(), None);
    }

    #[test]
    fn new_dcid_event() {
        let (scid, _) = create_cid_and_reset_token(16);
        let (dcid, _) = create_cid_and_reset_token(16);
        let network_path: FourTuple = (
            "1.2.3.4:8000".parse().unwrap(),
            "5.6.7.8:8008".parse().unwrap(),
        );

        let mut retired_path_ids = SmallVec::new();

        let mut ids = ConnectionIdentifiers::new(2, &scid, network_path, None);
        ids.set_initial_dcid(dcid, None, Some(network_path));

        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 1);

        let (dcid2, rt2) = create_cid_and_reset_token(16);

        assert_eq!(
            ids.new_dcid(0, dcid2, 1, rt2, 0, &mut retired_path_ids),
            Ok(()),
        );
        assert_eq!(retired_path_ids, SmallVec::from_buf([]));
        assert_eq!(ids.available_dcids(), 1);
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);

        // Now we assume that the client wants to advertise more source
        // Connection IDs than the advertised limit. This is valid if it
        // requests its peer to retire enough Connection IDs to fit within the
        // limits.
        let (dcid3, rt3) = create_cid_and_reset_token(16);
        assert_eq!(
            ids.new_dcid(0, dcid3, 2, rt3, 1, &mut retired_path_ids),
            Ok(())
        );
        assert_eq!(retired_path_ids, SmallVec::from_buf([(0, network_path)]));
        // The CID module does not handle path replacing. Fake it now.
        ids.link_dcid_to_network_path(0, 1, network_path).unwrap();
        assert_eq!(ids.available_dcids(), 1);
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);
        assert!(ids.has_retire_dcids());
        assert_eq!(ids.next_retire_dcid_seq(), Some((0, 0)));

        // Fake RETIRE_CONNECTION_ID sending.
        let _ = ids.mark_retire_dcid_seq(0, 0, false);
        assert!(!ids.has_retire_dcids());
        assert_eq!(ids.next_retire_dcid_seq(), None);

        // Now tries to experience CID retirement. If the server tries to remove
        // non-existing DCIDs, it fails.
        assert_eq!(ids.retire_dcid(0, 0), Err(Error::InvalidState));
        assert_eq!(ids.retire_dcid(0, 3), Err(Error::InvalidState));
        assert!(!ids.has_retire_dcids());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);

        // Now it removes DCID with sequence 1.
        assert_eq!(ids.retire_dcid(0, 1), Ok(Some(network_path)));
        // The CID module does not handle path replacing. Fake it now.
        ids.link_dcid_to_network_path(0, 2, network_path).unwrap();
        assert_eq!(ids.available_dcids(), 0);
        assert!(ids.has_retire_dcids());
        assert_eq!(ids.next_retire_dcid_seq(), Some((0, 1)));
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 1);

        // Fake RETIRE_CONNECTION_ID sending.
        let _ = ids.mark_retire_dcid_seq(0, 1, false);
        assert!(!ids.has_retire_dcids());
        assert_eq!(ids.next_retire_dcid_seq(), None);

        // Trying to remove the last DCID triggers an error.
        assert_eq!(ids.retire_dcid(0, 2), Err(Error::OutOfIdentifiers));
        assert_eq!(ids.available_dcids(), 0);
        assert!(!ids.has_retire_dcids());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 1);
    }

    #[test]
    fn new_dcid_reordered() {
        let (scid, _) = create_cid_and_reset_token(16);
        let (dcid, _) = create_cid_and_reset_token(16);
        let network_path: FourTuple = (
            "1.2.3.4:8000".parse().unwrap(),
            "5.6.7.8:8008".parse().unwrap(),
        );

        let mut retired_path_ids = SmallVec::new();

        let mut ids = ConnectionIdentifiers::new(2, &scid, network_path, None);
        ids.set_initial_dcid(dcid, None, Some(network_path));

        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 1);

        // Skip DCID #1 (e.g due to packet loss) and insert DCID #2.
        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 2, rt, 1, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 1);

        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 3, rt, 2, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);

        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 4, rt, 3, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);

        // Insert DCID #1 (e.g due to packet reordering).
        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 1, rt, 0, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);

        // Try inserting DCID #1 again (e.g. due to retransmission).
        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 1, rt, 0, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);
    }

    #[test]
    fn new_dcid_partial_retire_prior_to() {
        let (scid, _) = create_cid_and_reset_token(16);
        let (dcid, _) = create_cid_and_reset_token(16);
        let network_path: FourTuple = (
            "1.2.3.4:8000".parse().unwrap(),
            "5.6.7.8:8008".parse().unwrap(),
        );

        let mut retired_path_ids = SmallVec::new();

        let mut ids = ConnectionIdentifiers::new(5, &scid, network_path, None);
        ids.set_initial_dcid(dcid, None, Some(network_path));

        assert_eq!(ids.available_dcids(), 0);
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 1);

        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 1, rt, 0, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);

        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 2, rt, 0, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 3);

        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 3, rt, 0, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 4);

        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 4, rt, 0, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 5);

        // Retire a DCID from the middle of the list
        assert!(ids.retire_dcid(0, 3).is_ok());

        // Retire prior to DCID that was just retired.
        //
        // This is largely to test that the `partition_point()` call above
        // returns a meaningful value even if the actual sequence that is
        // searched isn't present in the list.
        let (dcid, rt) = create_cid_and_reset_token(16);
        assert!(ids
            .new_dcid(0, dcid, 5, rt, 3, &mut retired_path_ids)
            .is_ok());
        assert_eq!(ids.pcids.get_oldest().dcids.len(), 2);
    }

    #[test]
    fn retire_scids() {
        let (scid, _) = create_cid_and_reset_token(16);
        let (dcid, _) = create_cid_and_reset_token(16);
        let network_path: FourTuple = (
            "1.2.3.4:8000".parse().unwrap(),
            "5.6.7.8:8008".parse().unwrap(),
        );

        let mut ids = ConnectionIdentifiers::new(3, &scid, network_path, None);
        ids.set_initial_dcid(dcid, None, Some(network_path));
        ids.set_source_conn_id_limit(3);

        let (scid2, rt2) = create_cid_and_reset_token(16);
        let (scid3, rt3) = create_cid_and_reset_token(16);

        assert_eq!(
            ids.new_scid(0, scid2.clone(), Some(rt2), true, None, false),
            Ok(1),
        );
        assert_eq!(ids.pcids.get_oldest().scids.len(), 2);
        assert_eq!(
            ids.new_scid(0, scid3.clone(), Some(rt3), true, None, false),
            Ok(2),
        );
        assert_eq!(ids.pcids.get_oldest().scids.len(), 3);

        assert_eq!(ids.pop_retired_scid(), None);

        assert_eq!(ids.retire_scid(0, 0, &scid2), Ok(Some(network_path)));

        assert_eq!(ids.pop_retired_scid(), Some((0, scid)));
        assert_eq!(ids.pop_retired_scid(), None);

        assert_eq!(ids.retire_scid(0, 1, &scid3), Ok(None));

        assert_eq!(ids.pop_retired_scid(), Some((0, scid2)));
        assert_eq!(ids.pop_retired_scid(), None);
    }

    #[test]
    fn support_odd_path_ids() {
        let (scid, _) = create_cid_and_reset_token(16);
        let (dcid, _) = create_cid_and_reset_token(16);
        let network_path: FourTuple = (
            "1.2.3.4:8000".parse().unwrap(),
            "5.6.7.8:8008".parse().unwrap(),
        );

        let mut retired_path_ids = SmallVec::new();

        let mut ids = ConnectionIdentifiers::new(2, &scid, network_path, None);
        ids.set_initial_dcid(dcid, None, Some(network_path));

        ids.set_local_max_path_id(4, false);
        ids.set_remote_max_path_id(4);

        let (dcid1, rt1) = create_cid_and_reset_token(16);
        let (dcid2, rt2) = create_cid_and_reset_token(16);
        let (dcid3, rt3) = create_cid_and_reset_token(16);
        let (dcid4, rt4) = create_cid_and_reset_token(16);
        assert_eq!(
            ids.new_dcid(1, dcid1, 0, rt1, 0, &mut retired_path_ids),
            Ok(()),
        );
        assert_eq!(
            ids.new_dcid(2, dcid2, 0, rt2, 0, &mut retired_path_ids),
            Ok(()),
        );
        assert_eq!(
            ids.new_dcid(3, dcid3, 0, rt3, 0, &mut retired_path_ids),
            Ok(()),
        );
        assert_eq!(
            ids.new_dcid(4, dcid4, 0, rt4, 0, &mut retired_path_ids),
            Ok(()),
        );
    }
}
