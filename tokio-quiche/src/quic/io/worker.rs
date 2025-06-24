// Copyright (C) 2025, Cloudflare, Inc.
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

use std::collections::HashSet;
use std::net::SocketAddr;
use std::ops::ControlFlow;
use std::sync::Arc;
use std::task::Poll;
use std::time::Duration;
use std::time::Instant;
#[cfg(feature = "perf-quic-listener-metrics")]
use std::time::SystemTime;

use super::connection_stage::Close;
use super::connection_stage::ConnectionStage;
use super::connection_stage::ConnectionStageContext;
use super::connection_stage::Handshake;
use super::connection_stage::RunningApplication;
use super::gso::*;
use super::utilization_estimator::BandwidthReporter;

use crate::metrics::labels;
use crate::metrics::Metrics;
use crate::quic::connection::ApplicationOverQuic;
use crate::quic::connection::HandshakeError;
use crate::quic::connection::Incoming;
use crate::quic::connection::QuicConnectionStats;
use crate::quic::router::ConnectionMapCommand;
use crate::quic::scheduler::BoxedScheduler;
use crate::quic::QuicheConnection;
use crate::QuicResult;

use boring::ssl::SslRef;
use datagram_socket::DatagramSocketSend;
use datagram_socket::DatagramSocketSendExt;
use datagram_socket::MaybeConnectedSocket;
use datagram_socket::QuicAuditStats;
use foundations::telemetry::log;
use quiche::ConnectionId;
use quiche::Error as QuicheError;
use quiche::SendInfo;
use tokio::select;
use tokio::sync::mpsc;
use tokio::time;

// Number of incoming packets to be buffered in the incoming channel.
pub(crate) const INCOMING_QUEUE_SIZE: usize = 2048;

// Check if there are any incoming packets while sending data every this number
// of sent packets
pub(crate) const CHECK_INCOMING_QUEUE_RATIO: usize = INCOMING_QUEUE_SIZE / 16;

const RELEASE_TIMER_THRESHOLD: Duration = Duration::from_micros(250);

/// Stop queuing GSO packets, if packet size is below this threshold.
const GSO_THRESHOLD: usize = 1_000;

pub struct WriterConfig {
    /// Connection ID used during the handshake
    pub pending_cid: Option<ConnectionId<'static>>,
    /// Peer address used during the handshake
    pub peer_addr: SocketAddr,
    /// Whether to use GSO
    pub with_gso: bool,
    /// Whether to use GSO with pacing
    pub pacing_offload: bool,
    /// Whether there are packet info
    pub with_pktinfo: bool,
}

#[derive(Default)]
pub(crate) struct WriteState {
    /// Whether the connection has completed handshaking
    conn_established: bool,
    /// Number of bytes written for this path
    bytes_written: usize,
    /// Size of the segment written to the socket
    segment_size: usize,
    /// Number of packets prepared for this path
    num_pkts: usize,
    /// Scheduled transmit time for pacings
    tx_time: Option<Instant>,
    /// Whether there are pending data to send on any path
    has_pending_data: bool,
    // If pacer schedules packets too far into the future, we want to pause
    // sending, until the future arrives
    next_release_time: Option<Instant>,
    // If set, outgoing packets will be sent to the peer from the `send_from`
    // address rather than the listening socket.
    /// Socket address used as the source for outgoing packets
    send_from: Option<SocketAddr>,
    /// Socket address used as the destination for outgoing packets
    send_to: Option<SocketAddr>,
    /// Path identifier
    network_path_id: Option<usize>,
}

pub(crate) struct IoWorkerParams<Tx, M> {
    pub(crate) id: u64,
    pub(crate) sockets: Vec<MaybeConnectedSocket<Tx>>,
    pub(crate) shutdown_tx: mpsc::Sender<()>,
    pub(crate) cfg: WriterConfig,
    pub(crate) audit_log_stats: Arc<QuicAuditStats>,
    pub(crate) write_state: WriteState,
    pub(crate) conn_map_cmd_tx: mpsc::UnboundedSender<ConnectionMapCommand>,
    #[cfg(feature = "perf-quic-listener-metrics")]
    pub(crate) init_rx_time: Option<SystemTime>,
    pub(crate) metrics: M,
    pub(crate) packet_scheduler: Option<BoxedScheduler>,
}

pub(crate) struct IoWorker<Tx, M, S> {
    id: u64,
    sockets: Vec<MaybeConnectedSocket<Tx>>,
    /// A field that signals to the listener task that the connection has gone
    /// away (nothing is sent here, listener task just detects the sender
    /// has dropped)
    shutdown_tx: mpsc::Sender<()>,
    cfg: WriterConfig,
    audit_log_stats: Arc<QuicAuditStats>,
    write_state: WriteState,
    conn_map_cmd_tx: mpsc::UnboundedSender<ConnectionMapCommand>,
    #[cfg(feature = "perf-quic-listener-metrics")]
    init_rx_time: Option<SystemTime>,
    metrics: M,
    conn_stage: S,
    bw_estimator: BandwidthReporter,
    packet_scheduler: Option<BoxedScheduler>,
    known_cids: HashSet<ConnectionId<'static>>,
}

impl<Tx, M, S> IoWorker<Tx, M, S>
where
    Tx: DatagramSocketSend + Send,
    M: Metrics,
    S: ConnectionStage,
{
    pub(crate) fn new(params: IoWorkerParams<Tx, M>, conn_stage: S) -> Self {
        let bw_estimator =
            BandwidthReporter::new(params.metrics.utilized_bandwidth());

        log::trace!("Creating IoWorker with stage: {conn_stage:?}");

        Self {
            id: params.id,
            sockets: params.sockets,
            shutdown_tx: params.shutdown_tx,
            cfg: params.cfg,
            audit_log_stats: params.audit_log_stats,
            write_state: params.write_state,
            conn_map_cmd_tx: params.conn_map_cmd_tx,
            #[cfg(feature = "perf-quic-listener-metrics")]
            init_rx_time: params.init_rx_time,
            metrics: params.metrics,
            conn_stage,
            bw_estimator,
            packet_scheduler: params.packet_scheduler,
            known_cids: HashSet::new(),
        }
    }

    async fn work_loop<A: ApplicationOverQuic>(
        &mut self, qconn: &mut QuicheConnection,
        ctx: &mut ConnectionStageContext<A>,
    ) -> QuicResult<()> {
        const DEFAULT_SLEEP: Duration = Duration::from_secs(60);
        let mut current_deadline: Option<Instant> = None;
        let sleep = time::sleep(DEFAULT_SLEEP);
        tokio::pin!(sleep);

        loop {
            let now = Instant::now();

            self.write_state.has_pending_data = true;

            while self.write_state.has_pending_data {
                let mut packets_sent = 0;

                // Try to clear all received packets every so often, because
                // incoming packets contain acks, and because the
                // recieve queue has a very limited size, once it is full incoming
                // packets get stalled indefinitely
                let mut did_recv = false;
                while let Some(pkt) = ctx
                    .in_pkt
                    .take()
                    .or_else(|| ctx.incoming_pkt_receiver.try_recv().ok())
                {
                    self.process_incoming(qconn, pkt)?;
                    did_recv = true;
                }

                self.conn_stage.on_read(did_recv, qconn, ctx)?;
                self.process_path_events(qconn)?;
                self.sync_connection_ids(qconn)?;

                let can_release = match self.write_state.next_release_time {
                    None => true,
                    Some(next_release) =>
                        next_release
                            .checked_duration_since(now)
                            .unwrap_or_default() <
                            RELEASE_TIMER_THRESHOLD,
                };

                self.write_state.has_pending_data &= can_release;

                while self.write_state.has_pending_data &&
                    packets_sent < CHECK_INCOMING_QUEUE_RATIO
                {
                    self.gather_data_from_quiche_conn(qconn, ctx.buffer())?;

                    // Break if the connection is closed
                    if qconn.is_closed() {
                        return Ok(());
                    }

                    self.flush_buffer_to_socket(ctx.buffer()).await;
                    packets_sent += self.write_state.num_pkts;

                    if let ControlFlow::Break(reason) =
                        self.conn_stage.on_flush(qconn, ctx)
                    {
                        return reason;
                    }
                }
            }

            self.bw_estimator.update(qconn, now);

            let new_deadline = min_of_some(
                qconn.timeout_instant(),
                self.write_state.next_release_time,
            );
            let new_deadline =
                min_of_some(new_deadline, self.conn_stage.wait_deadline());

            if new_deadline != current_deadline {
                current_deadline = new_deadline;

                sleep
                    .as_mut()
                    .reset(new_deadline.unwrap_or(now + DEFAULT_SLEEP).into());
            }

            let incoming_recv = &mut ctx.incoming_pkt_receiver;
            let application = &mut ctx.application;
            select! {
                biased;
                () = &mut sleep => {
                    // It's very important that we keep the timeout arm at the top of this loop so
                    // that we poll it every time we need to. Since this is a biased `select!`, if
                    // we put this behind another arm, we could theoretically starve the sleep arm
                    // and hang connections.
                    //
                    // See https://docs.rs/tokio/latest/tokio/macro.select.html#fairness for more
                    qconn.on_timeout();

                    self.write_state.next_release_time = None;
                    current_deadline = None;
                    sleep.as_mut().reset((now + DEFAULT_SLEEP).into());
                }
                Some(pkt) = incoming_recv.recv() => ctx.in_pkt = Some(pkt),
                // TODO(erittenhouse): would be nice to decouple wait_for_data from the
                // application, but wait_for_quiche relies on IOW methods, so we can't write a
                // default implementation for ConnectionStage
                status = self.wait_for_data_or_handshake(qconn, application) => status?,
            };

            if let ControlFlow::Break(reason) = self.conn_stage.post_wait(qconn) {
                return reason;
            }
        }
    }

    #[inline]
    fn gather_data_from_quiche_conn(
        &mut self, qconn: &mut QuicheConnection, send_buf: &mut [u8],
    ) -> QuicResult<usize> {
        self.fill_send_buffer(qconn, send_buf)
    }

    #[cfg(feature = "perf-quic-listener-metrics")]
    fn measure_complete_handshake_time(&mut self) {
        if let Some(init_rx_time) = self.init_rx_time.take() {
            if let Ok(delta) = init_rx_time.elapsed() {
                self.metrics
                    .handshake_time_seconds(
                        labels::QuicHandshakeStage::HandshakeResponse,
                    )
                    .observe(delta.as_nanos() as u64);
            }
        }
    }

    fn fill_send_buffer(
        &mut self, qconn: &mut QuicheConnection, send_buf: &mut [u8],
    ) -> QuicResult<usize> {
        let mut segment_size = None;
        let mut send_info = None;

        self.write_state.num_pkts = 0;
        self.write_state.bytes_written = 0;

        let now = Instant::now();

        let send_buf = {
            let trunc = UDP_MAX_GSO_PACKET_SIZE.min(send_buf.len());
            &mut send_buf[..trunc]
        };

        #[cfg(feature = "gcongestion")]
        let next_release = {
            let next_release = qconn
                .get_next_release_time()
                .filter(|_| self.cfg.pacing_offload);

            if let Some(next_release) =
                next_release.as_ref().and_then(|v| v.time(now))
            {
                let max_into_fut = qconn.max_release_into_future();

                if next_release.duration_since(now) >= max_into_fut {
                    self.write_state.next_release_time =
                        Some(now + max_into_fut.mul_f32(0.8));
                    self.write_state.has_pending_data = false;
                    return Ok(0);
                }
            }

            next_release
        };

        let buffer_write_outcome = loop {
            let outcome = self.write_packet_to_buffer(
                qconn,
                send_buf,
                &mut send_info,
                segment_size,
            );

            let packet_size = match outcome {
                Ok(0) => {
                    self.write_state.has_pending_data = false;

                    break Ok(0);
                },
                Ok(bytes_written) => {
                    self.write_state.has_pending_data = true;

                    bytes_written
                },
                Err(e) => break Err(e),
            };

            // Flush to network after generating a single packet when GSO
            // is disabled.
            if !self.cfg.with_gso {
                break outcome;
            }

            #[cfg(not(feature = "gcongestion"))]
            let max_send_size = tune_max_send_size(
                segment_size,
                qconn.send_quantum(),
                send_buf.len(),
            );

            #[cfg(feature = "gcongestion")]
            let max_send_size = usize::MAX;

            // If segment_size is known, update the maximum of
            // GSO sender buffer size to the multiple of
            // segment_size.
            let buffer_is_full = self.write_state.num_pkts ==
                UDP_MAX_SEGMENT_COUNT ||
                self.write_state.bytes_written >= max_send_size;

            if buffer_is_full {
                break outcome;
            }

            // Flush to network when the newly generated packet size is
            // different from previously written packet, as GSO needs packets
            // to have the same size, except for the last one in the buffer.
            // The last packet may be smaller than the previous size.
            match segment_size {
                Some(size)
                    if packet_size != size || packet_size < GSO_THRESHOLD =>
                    break outcome,
                None => segment_size = Some(packet_size),
                _ => (),
            }

            #[cfg(feature = "gcongestion")]
            // If the release time of next packet is different, or it can't be
            // part of a burst, start the next batch
            if let Some(next_release) = next_release {
                match qconn.get_next_release_time() {
                    Some(release)
                        if release.can_burst() ||
                            release.time_eq(&next_release, now) => {},
                    _ => break outcome,
                }
            }
        };

        #[cfg(not(feature = "gcongestion"))]
        let tx_time = send_info.filter(|_| self.cfg.pacing_offload).map(|v| v.at);

        #[cfg(feature = "gcongestion")]
        let tx_time = next_release
            .filter(|_| self.cfg.pacing_offload)
            .and_then(|v| v.time(now));

        self.write_state.conn_established = qconn.is_established();
        self.write_state.tx_time = tx_time;
        self.write_state.segment_size =
            segment_size.unwrap_or(self.write_state.bytes_written);

        #[cfg(not(feature = "gcongestion"))]
        if let Some(time) = tx_time {
            const DEFAULT_MAX_INTO_FUTURE: Duration = Duration::from_millis(1);
            if time
                .checked_duration_since(now)
                .map(|d| d > DEFAULT_MAX_INTO_FUTURE)
                .unwrap_or(false)
            {
                self.write_state.next_release_time =
                    Some(now + DEFAULT_MAX_INTO_FUTURE.mul_f32(0.8));
                self.write_state.has_pending_data = false;
                return Ok(0);
            }
        }

        buffer_write_outcome
    }

    fn write_packet_to_buffer(
        &mut self, qconn: &mut QuicheConnection, send_buf: &mut [u8],
        send_info: &mut Option<SendInfo>, segment_size: Option<usize>,
    ) -> QuicResult<usize> {
        let mut send_buf = &mut send_buf[self.write_state.bytes_written..];
        if send_buf.len() > segment_size.unwrap_or(usize::MAX) {
            // Never let the buffer be longer than segment size, for GSO to
            // function properly
            send_buf = &mut send_buf[..segment_size.unwrap_or(usize::MAX)];
        }

        let multipath_enabled = qconn.is_multipath_enabled() &&
            qconn.is_established() &&
            qconn.is_handshake_confirmed();

        if multipath_enabled {
            if let Some(scheduler) = &mut self.packet_scheduler {
                if let Some((local_addr, peer_addr)) = scheduler.next_path(qconn)
                {
                    match qconn.send_on_path(
                        send_buf,
                        None,
                        Some(local_addr),
                        Some(peer_addr),
                    ) {
                        Ok((packet_size, info)) => {
                            let _ = send_info.get_or_insert(info);
                            let send_from =
                                send_info.as_ref().map(|info| info.from);
                            let send_to = send_info.as_ref().map(|info| info.to);

                            self.write_state.bytes_written += packet_size;
                            self.write_state.num_pkts += 1;
                            self.write_state.send_from = send_from;
                            self.write_state.send_to = send_to;
                            let network_path_id = qconn
                                .network_path_id_from(
                                    send_from.unwrap(),
                                    send_to.unwrap(),
                                )
                                .map(|id| id as usize); // TODO: check the Option
                            self.write_state.network_path_id = network_path_id;

                            return Ok(packet_size);
                        },
                        Err(QuicheError::Done) => {
                            // Flush to network and yield when there are no
                            // more packets to write.
                            return Ok(0);
                        },
                        Err(e) => {
                            let error_code = if let Some(local_error) =
                                qconn.local_error()
                            {
                                local_error.error_code
                            } else {
                                let internal_error_code =
                                    quiche::WireErrorCode::InternalError as u64;
                                let _ =
                                    qconn.close(false, internal_error_code, &[]);

                                internal_error_code
                            };

                            self.audit_log_stats
                                .set_sent_conn_close_transport_error_code(
                                    error_code as i64,
                                );

                            return Err(Box::new(e));
                        },
                    }
                }
            }
        }

        match qconn.send(send_buf) {
            Ok((packet_size, info)) => {
                let _ = send_info.get_or_insert(info);
                let send_from = send_info.as_ref().map(|info| info.from);
                let send_to = send_info.as_ref().map(|info| info.to);

                self.write_state.bytes_written += packet_size;
                self.write_state.num_pkts += 1;
                self.write_state.send_from = send_from;
                self.write_state.send_to = send_to;
                let network_path_id = qconn
                    .network_path_id_from(send_from.unwrap(), send_to.unwrap())
                    .map(|id| id as usize); // TODO: check the Option
                self.write_state.network_path_id = network_path_id;

                Ok(packet_size)
            },
            Err(QuicheError::Done) => {
                // Flush to network and yield when there are no
                // more packets to write.
                Ok(0)
            },
            Err(e) => {
                let error_code = if let Some(local_error) = qconn.local_error() {
                    local_error.error_code
                } else {
                    let internal_error_code =
                        quiche::WireErrorCode::InternalError as u64;
                    let _ = qconn.close(false, internal_error_code, &[]);

                    internal_error_code
                };

                self.audit_log_stats
                    .set_sent_conn_close_transport_error_code(error_code as i64);

                Err(Box::new(e))
            },
        }
    }

    async fn flush_buffer_to_socket(&mut self, send_buf: &[u8]) {
        if self.write_state.bytes_written > 0 {
            let current_send_buf = &send_buf[..self.write_state.bytes_written];

            // Select the socket based on path_id if available
            let socket_index =
                if let Some(path_id) = self.write_state.network_path_id {
                    // Ensure path_id is within bounds (default to first socket if
                    // not)
                    if path_id < self.sockets.len() {
                        path_id
                    } else {
                        log::warn!(
                            "Path ID {} is out of bounds, using socket 0",
                            path_id
                        );
                        0
                    }
                } else {
                    // No path_id, use the first socket
                    0
                };

            let socket = &self.sockets[socket_index];
            let peer_addr = self.write_state.send_to.unwrap_or_else(|| {
                // Default to the peer address if send_to is not set
                self.cfg.peer_addr
            });

            let send_res = if let (Some(udp_socket), true) =
                (socket.as_udp_socket(), self.cfg.with_gso)
            {
                // Only UDP supports GSO
                send_to(
                    udp_socket,
                    peer_addr,
                    self.write_state.send_from.filter(|_| self.cfg.with_pktinfo),
                    current_send_buf,
                    self.write_state.segment_size,
                    self.write_state.num_pkts,
                    self.write_state.tx_time,
                )
                .await
            } else {
                socket.send_to(current_send_buf, peer_addr).await
            };

            #[cfg(feature = "perf-quic-listener-metrics")]
            self.measure_complete_handshake_time();

            match send_res {
                Ok(n) =>
                    if n < self.write_state.bytes_written {
                        self.metrics
                            .write_errors(labels::QuicWriteError::Partial)
                            .inc();
                    },
                Err(_) => {
                    self.metrics.write_errors(labels::QuicWriteError::Err).inc();
                },
            }
        }
    }

    fn sync_connection_ids(
        &mut self, qconn: &mut QuicheConnection,
    ) -> QuicResult<()> {
        let mut current_cids = HashSet::new();

        // Process all current source IDs
        for cid in qconn.source_ids() {
            let owned_cid = cid.clone().into_owned();
            current_cids.insert(owned_cid.clone());

            // Only send MapCid if this is a new CID we haven't mapped before
            if !self.known_cids.contains(&owned_cid) {
                log::trace!(
                    "Mapping new SCID {:?} to connection ID {}",
                    owned_cid,
                    self.id
                );
                let _ = self.conn_map_cmd_tx.send(ConnectionMapCommand::MapCid(
                    owned_cid.clone(),
                    self.id,
                ));
                self.known_cids.insert(owned_cid);
            }
        }

        // Process all retired SCIDs
        while let Some((path_id, retired_scid)) =
            qconn.retired_scid_on_path_next()
        {
            let owned_scid = retired_scid.into_owned();
            log::trace!("Retired SCID {:?} on path ID {}", owned_scid, path_id);

            // Remove from our known set and send unmap command
            self.known_cids.remove(&owned_scid);
            let _ = self
                .conn_map_cmd_tx
                .send(ConnectionMapCommand::UnmapCid(owned_scid));
        }

        // Check for CIDs that were previously known but are no longer in the
        // current set This is a fallback mechanism in case
        // retired_scid_on_path_next() missed something
        let missing_cids: Vec<_> = self
            .known_cids
            .iter()
            .filter(|cid| !current_cids.contains(*cid))
            .cloned()
            .collect();

        for missing_cid in missing_cids {
            log::trace!(
                "CID {:?} is no longer active but wasn't explicitly retired",
                missing_cid
            );
            self.known_cids.remove(&missing_cid);
            let _ = self
                .conn_map_cmd_tx
                .send(ConnectionMapCommand::UnmapCid(missing_cid));
        }

        Ok(())
    }

    /// Process the incoming packet
    fn process_incoming(
        &mut self, qconn: &mut QuicheConnection, mut pkt: Incoming,
    ) -> QuicResult<()> {
        let recv_info = quiche::RecvInfo {
            from: pkt.peer_addr,
            to: pkt.local_addr,
        };

        if let Some(gro) = pkt.gro {
            for dgram in pkt.buf.chunks_mut(gro as usize) {
                qconn.recv(dgram, recv_info)?;
            }
        } else {
            qconn.recv(&mut pkt.buf, recv_info)?;
        }

        Ok(())
    }

    /// Process all pending path events
    fn process_path_events(
        &mut self, qconn: &mut QuicheConnection,
    ) -> QuicResult<()> {
        while let Some((path_id, event)) = qconn.path_event_next() {
            match event {
                quiche::PathEvent::New(local_addr, peer_addr) => {
                    log::info!(
                        "Seen new path ({}, {}) with ID {}",
                        local_addr,
                        peer_addr,
                        path_id
                    );

                    // If we're a server, we need to probe back the path in
                    // response
                    if qconn.is_server() && qconn.is_multipath_enabled() {
                        if let Err(e) =
                            qconn.probe_path(path_id, local_addr, peer_addr)
                        {
                            log::error!(
                                "Cannot probe path ({},{}): {}",
                                local_addr,
                                peer_addr,
                                e
                            );
                        }
                    }
                },

                quiche::PathEvent::Validated(local_addr, peer_addr) => {
                    log::info!(
                        "Path ({}, {}) with ID {} is now validated",
                        local_addr,
                        peer_addr,
                        path_id
                    );

                    // Activate the path for multipath connections
                    if qconn.is_multipath_enabled() {
                        if let Err(e) = qconn.set_active(path_id, true) {
                            log::error!(
                                "Cannot set path active ({},{}): {}",
                                local_addr,
                                peer_addr,
                                e
                            );
                        }
                    }
                },

                quiche::PathEvent::FailedValidation(local_addr, peer_addr) => {
                    log::info!(
                        "Path ({}, {}) with ID {} failed validation",
                        local_addr,
                        peer_addr,
                        path_id
                    );
                },

                quiche::PathEvent::Closed(local_addr, peer_addr, err) => {
                    log::info!(
                        "Path ({}, {}) with ID {} is now closed and unusable; err = {}",
                        local_addr,
                        peer_addr,
                        path_id,
                        err,
                    );
                },

                quiche::PathEvent::ReusedSourceConnectionId(
                    cid_seq,
                    old,
                    new,
                ) => {
                    log::info!(
                        "Peer reused cid seq {} (initially {:?}) on {:?} on path ID {}",
                        cid_seq, old, new, path_id
                    );
                },

                quiche::PathEvent::PeerMigrated(local_addr, peer_addr) => {
                    log::info!(
                        "Connection migrated to ({}, {}) on Path ID {}",
                        local_addr,
                        peer_addr,
                        path_id
                    );
                    // TODO: Update routing map if needed
                },

                quiche::PathEvent::PeerPathStatus(addr, path_status) => {
                    log::info!(
                        "Peer asks status {:?} for {:?} on path ID {}",
                        path_status,
                        addr,
                        path_id
                    );

                    if let Err(e) =
                        qconn.set_path_status(path_id, path_status, false)
                    {
                        log::error!("Cannot follow status request: {}", e);
                    }
                },
            }
        }

        Ok(())
    }

    /// When a connection is established, process application data, if not the
    /// task is probably polled following a wakeup from boring, so we check
    /// if quiche has any handshake packets to send.
    async fn wait_for_data_or_handshake<A: ApplicationOverQuic>(
        &mut self, qconn: &mut QuicheConnection, quic_application: &mut A,
    ) -> QuicResult<()> {
        if quic_application.should_act() {
            quic_application.wait_for_data(qconn).await
        } else {
            self.wait_for_quiche(qconn, quic_application).await
        }
    }

    /// Check if Quiche has any packets to send and flush them to socket.
    ///
    /// # Example
    ///
    /// This function can be used, for example, to drive an asynchronous TLS
    /// handshake. Each call to `gather_data_from_quiche_conn` attempts to
    /// progress the handshake via a call to `quiche::Connection.send()` -
    /// once one of the `gather_data_from_quiche_conn()` calls writes to the
    /// send buffer, we flush it to the network socket.
    async fn wait_for_quiche<App: ApplicationOverQuic>(
        &mut self, qconn: &mut QuicheConnection, app: &mut App,
    ) -> QuicResult<()> {
        let populate_send_buf = std::future::poll_fn(|_| {
            match self.gather_data_from_quiche_conn(qconn, app.buffer()) {
                Ok(bytes_written) => {
                    // We need to avoid consecutive calls to gather(), which write
                    // data to the buffer, without a flush().
                    // If we don't avoid those consecutive calls, we end
                    // up overwriting data in the buffer or unnecessarily waiting
                    // for more calls to drive_handshake()
                    // before calling the handshake complete.
                    if bytes_written == 0 && self.write_state.bytes_written == 0 {
                        Poll::Pending
                    } else {
                        Poll::Ready(Ok(()))
                    }
                },
                _ => Poll::Ready(Err(quiche::Error::TlsFail)),
            }
        })
        .await;

        if populate_send_buf.is_err() {
            return Err(Box::new(quiche::Error::TlsFail));
        }

        self.flush_buffer_to_socket(app.buffer()).await;

        Ok(())
    }
}

pub struct Running<Tx, M, A> {
    pub(crate) params: IoWorkerParams<Tx, M>,
    pub(crate) context: ConnectionStageContext<A>,
    pub(crate) qconn: QuicheConnection,
}

impl<Tx, M, A> Running<Tx, M, A> {
    pub fn ssl(&mut self) -> &mut SslRef {
        self.qconn.as_mut()
    }
}

pub(crate) struct Closing<Tx, M, A> {
    pub(crate) params: IoWorkerParams<Tx, M>,
    pub(crate) context: ConnectionStageContext<A>,
    pub(crate) work_loop_result: QuicResult<()>,
    pub(crate) qconn: QuicheConnection,
}

pub enum RunningOrClosing<Tx, M, A> {
    Running(Running<Tx, M, A>),
    Closing(Closing<Tx, M, A>),
}

impl<Tx, M> IoWorker<Tx, M, Handshake>
where
    Tx: DatagramSocketSend + Send,
    M: Metrics,
{
    pub(crate) async fn run<A>(
        mut self, mut qconn: QuicheConnection, mut ctx: ConnectionStageContext<A>,
    ) -> RunningOrClosing<Tx, M, A>
    where
        A: ApplicationOverQuic,
    {
        // This makes an assumption that the waker being set in ex_data is stable
        // accross the active task's lifetime. Moving a future that encompasses an
        // async callback from this task accross a channel, for example, will
        // cause issues as this waker will then be stale and attempt to
        // wake the wrong task.
        std::future::poll_fn(|cx| {
            let ssl = qconn.as_mut();
            ssl.set_task_waker(Some(cx.waker().clone()));

            Poll::Ready(())
        })
        .await;

        let mut work_loop_result = self.work_loop(&mut qconn, &mut ctx).await;
        if work_loop_result.is_ok() && qconn.is_closed() {
            work_loop_result = Err(HandshakeError::ConnectionClosed.into());
        }

        if let Err(err) = &work_loop_result {
            self.metrics.failed_handshakes(err.into()).inc();

            return RunningOrClosing::Closing(Closing {
                params: self.into(),
                context: ctx,
                work_loop_result,
                qconn,
            });
        };

        match self.on_conn_established(&mut qconn, &mut ctx.application) {
            Ok(()) => RunningOrClosing::Running(Running {
                params: self.into(),
                context: ctx,
                qconn,
            }),
            Err(e) => {
                foundations::telemetry::log::warn!(
                    "Handshake stage on_connection_established failed"; "error"=>%e
                );

                RunningOrClosing::Closing(Closing {
                    params: self.into(),
                    context: ctx,
                    work_loop_result,
                    qconn,
                })
            },
        }
    }

    fn on_conn_established<App: ApplicationOverQuic>(
        &mut self, qconn: &mut QuicheConnection, driver: &mut App,
    ) -> QuicResult<()> {
        // Only calculate the QUIC handshake duration and call the driver's
        // on_conn_established hook if this is the first time
        // is_established == true.
        if self.audit_log_stats.transport_handshake_duration_us() == -1 {
            self.conn_stage.handshake_info.set_elapsed();
            let handshake_info = &self.conn_stage.handshake_info;

            self.audit_log_stats
                .set_transport_handshake_duration(handshake_info.elapsed());

            driver.on_conn_established(qconn, handshake_info)?;
        }

        if let Some(cid) = self.cfg.pending_cid.take() {
            let _ = self
                .conn_map_cmd_tx
                .send(ConnectionMapCommand::UnmapCid(cid));
        }

        Ok(())
    }
}

impl<Tx, M, S> From<IoWorker<Tx, M, S>> for IoWorkerParams<Tx, M> {
    fn from(value: IoWorker<Tx, M, S>) -> Self {
        Self {
            id: value.id,
            sockets: value.sockets,
            shutdown_tx: value.shutdown_tx,
            cfg: value.cfg,
            audit_log_stats: value.audit_log_stats,
            write_state: value.write_state,
            conn_map_cmd_tx: value.conn_map_cmd_tx,
            #[cfg(feature = "perf-quic-listener-metrics")]
            init_rx_time: value.init_rx_time,
            metrics: value.metrics,
            packet_scheduler: value.packet_scheduler,
        }
    }
}

impl<Tx, M> IoWorker<Tx, M, RunningApplication>
where
    Tx: DatagramSocketSend + Send,
    M: Metrics,
{
    pub(crate) async fn run<A: ApplicationOverQuic>(
        mut self, mut qconn: QuicheConnection, mut ctx: ConnectionStageContext<A>,
    ) -> Closing<Tx, M, A> {
        let work_loop_result = self.work_loop(&mut qconn, &mut ctx).await;

        Closing {
            params: self.into(),
            context: ctx,
            work_loop_result,
            qconn,
        }
    }
}

impl<Tx, M> IoWorker<Tx, M, Close>
where
    Tx: DatagramSocketSend + Send,
    M: Metrics,
{
    pub(crate) async fn close<A: ApplicationOverQuic>(
        mut self, qconn: &mut QuicheConnection,
        ctx: &mut ConnectionStageContext<A>,
    ) {
        if self.conn_stage.work_loop_result.is_ok() &&
            self.bw_estimator.max_bandwidth > 0
        {
            let metrics = &self.metrics;

            metrics
                .max_bandwidth_mbps()
                .observe(self.bw_estimator.max_bandwidth as f64 * 1e-6);

            metrics
                .max_loss_pct()
                .observe(self.bw_estimator.max_loss_pct as f64 * 100.);
        }

        if ctx.application.should_act() {
            ctx.application.on_conn_close(
                qconn,
                &self.metrics,
                &self.conn_stage.work_loop_result,
            );
        }

        // TODO: this assumes that the tidy_up operation can be completed in one
        // send (ignoring flow/congestion control constraints). We should
        // guarantee that it gets sent by doublechecking the
        // gathered/flushed byte totals and retry if they don't match.
        let _ = self.gather_data_from_quiche_conn(qconn, ctx.buffer());
        self.flush_buffer_to_socket(ctx.buffer()).await;

        *ctx.stats.lock().unwrap() = QuicConnectionStats::from_conn(qconn);

        if let Some(err) = qconn.peer_error() {
            if err.is_app {
                self.audit_log_stats
                    .set_recvd_conn_close_application_error_code(
                        err.error_code as _,
                    );
            } else {
                self.audit_log_stats
                    .set_recvd_conn_close_transport_error_code(
                        err.error_code as _,
                    );
            }
        }

        self.close_connection(qconn);

        if let Err(work_loop_error) = self.conn_stage.work_loop_result {
            self.audit_log_stats
                .set_connection_close_reason(work_loop_error);
        }
    }

    fn close_connection(&mut self, qconn: &QuicheConnection) {
        let scid = qconn.source_id().into_owned();

        if let Some(cid) = self.cfg.pending_cid.take() {
            let _ = self
                .conn_map_cmd_tx
                .send(ConnectionMapCommand::UnmapCid(cid));
        }

        let _ = self
            .conn_map_cmd_tx
            .send(ConnectionMapCommand::RemoveScid(scid));

        self.metrics.connections_in_memory().dec();
    }
}

/// Returns the minimum of `v1` and `v2`, ignoring `None`s.
fn min_of_some<T: Ord>(v1: Option<T>, v2: Option<T>) -> Option<T> {
    match (v1, v2) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (Some(v), _) | (_, Some(v)) => Some(v),
        (None, None) => None,
    }
}
