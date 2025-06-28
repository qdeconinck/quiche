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

use std::future::Future;
use std::io;
use std::pin::Pin;
use std::sync::Arc;
use std::task::Context;
use std::task::Poll;
use std::time::SystemTime;

use datagram_socket::DatagramSocketRecv;
use datagram_socket::DatagramSocketSend;
use task_killswitch::spawn_with_killswitch;
use tokio::sync::mpsc;

use crate::buf_factory::BufFactory;
use crate::buf_factory::PooledBuf;
use crate::metrics::labels;
use crate::metrics::quic_expensive_metrics_ip_reduce;
use crate::metrics::Metrics;
use crate::quic::connection::InitialQuicConnection;
use crate::quic::router::initial_packet_error_type;
use crate::quic::router::short_dcid;
use crate::quic::router::ConnStream;
use crate::quic::router::ConnectionMap;
use crate::quic::router::ConnectionMapCommand;
use crate::quic::router::InitialPacketHandler;
use crate::quic::router::PollRecvData;
use crate::quic::Incoming;
use crate::settings::Config;

/// A router that can handle incoming packets from multiple network paths.
pub struct MultiPathInboundRouter<Tx, Rx, M, I>
where
    Tx: DatagramSocketSend + Send + 'static,
    M: Metrics,
{
    // Shared connection map
    conns: ConnectionMap,

    // Path information
    path_rxs: Vec<(Rx, std::net::SocketAddr)>, // (receiver, local_addr) pairs
    path_txs: Vec<Arc<Tx>>,                    // Shared senders for all paths

    // Primary path info (for backward compatibility)
    primary_local_addr: std::net::SocketAddr,

    // Connection management
    incoming_packet_handler: I,
    shutdown_tx: Option<mpsc::Sender<()>>,
    shutdown_rx: mpsc::Receiver<()>,
    conn_map_cmd_tx: mpsc::UnboundedSender<ConnectionMapCommand>,
    conn_map_cmd_rx: mpsc::UnboundedReceiver<ConnectionMapCommand>,
    accept_sink: mpsc::Sender<io::Result<InitialQuicConnection<Tx, M>>>,

    // Configuration and metrics
    config: Config,
    metrics: M,

    // Buffer management
    buffers: Vec<PooledBuf>, // One buffer per path

    // Platform-specific metrics
    #[cfg(target_os = "linux")]
    metrics_handshake_time_seconds:
        foundations::telemetry::metrics::TimeHistogram,
    #[cfg(target_os = "linux")]
    metrics_udp_drop_count: foundations::telemetry::metrics::Counter,
    #[cfg(target_os = "linux")]
    udp_drop_counts: Vec<u32>, // One per path
    #[cfg(target_os = "linux")]
    reusable_cmsg_spaces: Vec<Vec<u8>>, // One per path
}

impl<Tx, Rx, M, I> MultiPathInboundRouter<Tx, Rx, M, I>
where
    Tx: DatagramSocketSend + Send + 'static,
    Rx: DatagramSocketRecv,
    M: Metrics,
    I: InitialPacketHandler,
{
    /// Creates a new multipath router for handling packets from multiple
    /// network paths.
    pub fn new(
        config: Config, path_txs: Vec<Arc<Tx>>,
        path_rxs: Vec<(Rx, std::net::SocketAddr)>,
        primary_local_addr: std::net::SocketAddr, incoming_packet_handler: I,
        metrics: M,
    ) -> (Self, ConnStream<Tx, M>) {
        // Validate input
        assert!(!path_rxs.is_empty(), "At least one path is required");

        let (shutdown_tx, shutdown_rx) = mpsc::channel(1);
        let (accept_sink, accept_stream) = mpsc::channel(config.listen_backlog);
        let (conn_map_cmd_tx, conn_map_cmd_rx) = mpsc::unbounded_channel();

        // Create a buffer for each path
        let buffers: Vec<_> = (0..path_rxs.len())
            .map(|_| BufFactory::get_max_buf())
            .collect();

        #[cfg(target_os = "linux")]
        let udp_drop_counts = vec![0; path_rxs.len()];

        #[cfg(target_os = "linux")]
        let reusable_cmsg_spaces: Vec<Vec<u8>> = (0..path_rxs.len())
            .map(|_| {
                nix::cmsg_space!(
                    u32,
                    nix::sys::time::TimeSpec,
                    u16,
                    nix::sys::socket::sockaddr_in,
                    nix::sys::socket::sockaddr_in6
                )
            })
            .collect();

        (
            MultiPathInboundRouter {
                conns: ConnectionMap::default(),
                path_rxs,
                path_txs,
                primary_local_addr,
                incoming_packet_handler,
                shutdown_tx: Some(shutdown_tx),
                shutdown_rx,
                conn_map_cmd_tx,
                conn_map_cmd_rx,
                accept_sink,
                config,
                buffers,
                #[cfg(target_os = "linux")]
                metrics_handshake_time_seconds: metrics.handshake_time_seconds(
                    labels::QuicHandshakeStage::QueueWaiting,
                ),
                #[cfg(target_os = "linux")]
                metrics_udp_drop_count: metrics.udp_drop_count(),
                #[cfg(target_os = "linux")]
                udp_drop_counts,
                #[cfg(target_os = "linux")]
                reusable_cmsg_spaces,
                metrics,
            },
            accept_stream,
        )
    }

    /// Process an incoming packet from any path
    fn on_incoming(&mut self, mut incoming: Incoming) -> io::Result<()> {
        #[cfg(feature = "perf-quic-listener-metrics")]
        let start = std::time::Instant::now();

        // Try to route based on short header DCID
        if let Some(dcid) = short_dcid(&incoming.buf) {
            if let Some(ev_sender) = self.conns.get(&dcid) {
                let _ = ev_sender.try_send(incoming);
                return Ok(());
            }
        }

        // If not a short header or unknown connection, parse as long header
        let hdr = quiche::Header::from_slice(
            &mut incoming.buf,
            quiche::MAX_CONN_ID_LEN,
        )
        .map_err(|e| match e {
            quiche::Error::BufferTooShort =>
                labels::QuicInvalidInitialPacketError::SmallPacket.into(),
            e => io::Error::other(e),
        })?;

        // Try to route based on long header DCID
        if let Some(ev_sender) = self.conns.get(&hdr.dcid) {
            let _ = ev_sender.try_send(incoming);
            return Ok(());
        }

        #[cfg(feature = "perf-quic-listener-metrics")]
        let _timer =
            crate::quic::router::listener_stage_timer::ListenerStageTimer::new(
                start,
                self.metrics.handshake_time_seconds(
                    labels::QuicHandshakeStage::HandshakeProtocol,
                ),
            );

        // Don't create new connections if we're shutting down
        if self.shutdown_tx.is_none() {
            return Ok(());
        }

        let local_addr = incoming.local_addr;
        let peer_addr = incoming.peer_addr;

        #[cfg(feature = "perf-quic-listener-metrics")]
        let init_rx_time = incoming.rx_time;

        // Let the InitialPacketHandler process this new connection
        let new_connection = self.incoming_packet_handler.handle_initials(
            incoming,
            hdr,
            self.config.as_mut(),
        )?;

        match new_connection {
            Some(new_connection) => self.spawn_new_connection(
                new_connection,
                local_addr,
                peer_addr,
                #[cfg(feature = "perf-quic-listener-metrics")]
                init_rx_time,
            ),
            None => Ok(()),
        }
    }

    /// Creates a new [`QuicConnection`] and spawns an associated io worker.
    ///
    /// This is similar to the original InboundPacketRouter's
    /// spawn_new_connection but modified to pass the multipath txs.
    fn spawn_new_connection(
        &mut self, new_connection: crate::quic::router::NewConnection,
        _local_addr: std::net::SocketAddr, peer_addr: std::net::SocketAddr,
        #[cfg(feature = "perf-quic-listener-metrics")] init_rx_time: Option<
            SystemTime,
        >,
    ) -> io::Result<()> {
        let crate::quic::router::NewConnection {
            conn,
            pending_cid,
            handshake_start_time,
            initial_pkt,
        } = new_connection;

        // Don't create new connections if we're shutting down
        let Some(ref shutdown_tx) = self.shutdown_tx else {
            return Ok(());
        };

        // Check if we have room for a new connection
        let Ok(send_permit) = self.accept_sink.try_reserve() else {
            return Err(
                labels::QuicInvalidInitialPacketError::AcceptQueueOverflow.into(),
            );
        };

        let scid = conn.source_id().into_owned();
        let writer_cfg = crate::quic::io::worker::WriterConfig {
            peer_addr,
            pending_cid: pending_cid.clone(),
            with_gso: self.config.has_gso,
            pacing_offload: self.config.pacing_offload,
            with_pktinfo: if self.primary_local_addr.is_ipv4() {
                self.config.has_ippktinfo
            } else {
                self.config.has_ipv6pktinfo
            },
        };

        let handshake_info = crate::quic::connection::HandshakeInfo::new(
            handshake_start_time,
            self.config.handshake_timeout,
        );

        // Create a new InitialQuicConnection with multipath support
        // We need to create a new struct to hold multipath information
        let conn = InitialQuicConnection::new(
            crate::quic::connection::QuicConnectionParams {
                writer_cfg,
                initial_pkt,
                shutdown_tx: shutdown_tx.clone(),
                conn_map_cmd_tx: self.conn_map_cmd_tx.clone(),
                scid: scid.clone(),
                metrics: self.metrics.clone(),
                #[cfg(feature = "perf-quic-listener-metrics")]
                init_rx_time,
                handshake_info,
                quiche_conn: conn,
                sockets: self.path_txs.clone(),
                local_addrs: self
                    .path_rxs
                    .iter()
                    .map(|(_, addr)| *addr)
                    .collect(),
                peer_addr,
                packet_scheduler: self.config.packet_scheduler.clone(),
            },
        );

        conn.audit_log_stats.set_transport_handshake_start(
            crate::quic::router::instant_to_system(handshake_start_time),
        );

        self.conns.insert(scid, &conn);

        // Add the client-generated "pending" connection ID to the map as well.
        if let Some(pending_cid) = pending_cid {
            self.conns.map_cid(pending_cid, &conn);
        }

        self.metrics.accepted_initial_packet_count().inc();
        if self.config.enable_expensive_packet_count_metrics {
            if let Some(peer_ip) =
                quic_expensive_metrics_ip_reduce(conn.peer_addr().ip())
            {
                self.metrics
                    .expensive_accepted_initial_packet_count(peer_ip)
                    .inc();
            }
        }

        send_permit.send(Ok(conn));
        Ok(())
    }
}

impl<Tx, Rx, M, I> MultiPathInboundRouter<Tx, Rx, M, I>
where
    Tx: DatagramSocketSend + Send + Sync + 'static,
    Rx: DatagramSocketRecv,
    M: Metrics,
    I: InitialPacketHandler,
{
    // Poll a single path for incoming data
    fn poll_path(
        &mut self, cx: &mut Context<'_>, path_id: usize,
    ) -> Poll<io::Result<PollRecvData>> {
        #[cfg(not(target_os = "linux"))]
        {
            // Simple polling for non-Linux platforms
            let (ref mut rx, _) = self.path_rxs[path_id];
            let mut buf = tokio::io::ReadBuf::new(&mut self.buffers[path_id]);

            match rx.poll_recv_from(cx, &mut buf) {
                Poll::Ready(Ok(peer_addr)) => {
                    let bytes = buf.filled().len();

                    let mut buf = std::mem::replace(
                        &mut self.buffers[path_id],
                        BufFactory::get_max_buf(),
                    );
                    buf.truncate(bytes);

                    Poll::Ready(Ok(PollRecvData {
                        bytes,
                        src_addr: peer_addr,
                        dst_addr_override: None,
                        rx_time: None,
                        gro: None,
                        path_id: path_id as u64,
                    }))
                },
                Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
                Poll::Pending => Poll::Pending,
            }
        }

        #[cfg(target_os = "linux")]
        {
            use nix::errno::Errno;
            use nix::sys::socket::*;
            use std::net::SocketAddrV4;
            use std::net::SocketAddrV6;
            use std::os::fd::AsRawFd;
            use std::task::ready;
            use tokio::io::Interest;

            let (ref rx, local_addr) = self.path_rxs[path_id];

            // First, we need a UDP socket to work with
            let Some(udp_socket) = rx.as_udp_socket() else {
                // If it's not a UDP socket, use the simple recv_from method
                // instead
                return self.poll_path_simple(cx, path_id);
            };

            self.reusable_cmsg_spaces[path_id].clear();

            loop {
                let iov_s =
                    &mut [io::IoSliceMut::new(&mut self.buffers[path_id])];
                match udp_socket.try_io(Interest::READABLE, || {
                    recvmsg::<SockaddrStorage>(
                        udp_socket.as_raw_fd(),
                        iov_s,
                        Some(&mut self.reusable_cmsg_spaces[path_id]),
                        MsgFlags::empty(),
                    )
                    .map_err(|x| x.into())
                }) {
                    Ok(r) => {
                        let bytes = r.bytes;

                        let address = match r.address {
                            Some(inner) => inner,
                            _ => return Poll::Ready(Err(Errno::EINVAL.into())),
                        };

                        let peer_addr = match address.family() {
                            Some(AddressFamily::Inet) => SocketAddrV4::from(
                                *address.as_sockaddr_in().unwrap(),
                            )
                            .into(),
                            Some(AddressFamily::Inet6) => SocketAddrV6::from(
                                *address.as_sockaddr_in6().unwrap(),
                            )
                            .into(),
                            _ => {
                                return Poll::Ready(Err(Errno::EINVAL.into()));
                            },
                        };

                        let mut rx_time = None;
                        let mut gro = None;
                        let mut dst_addr_override = None;

                        for cmsg in r.cmsgs() {
                            match cmsg {
                                ControlMessageOwned::RxqOvfl(c) => {
                                    if c != self.udp_drop_counts[path_id] {
                                        self.metrics_udp_drop_count.inc_by(
                                            (c - self.udp_drop_counts[path_id])
                                                as u64,
                                        );
                                        self.udp_drop_counts[path_id] = c;
                                    }
                                },
                                ControlMessageOwned::ScmTimestampns(val) => {
                                    rx_time = SystemTime::UNIX_EPOCH
                                        .checked_add(val.into());
                                    if let Some(delta) =
                                        rx_time.and_then(|rx_time| {
                                            rx_time.elapsed().ok()
                                        })
                                    {
                                        self.metrics_handshake_time_seconds
                                            .observe(delta.as_nanos() as u64);
                                    }
                                },
                                ControlMessageOwned::UdpGroSegments(val) => {
                                    gro = Some(val);
                                },
                                ControlMessageOwned::Ipv4OrigDstAddr(val) => {
                                    let source_addr = std::net::Ipv4Addr::from(
                                        u32::to_be(val.sin_addr.s_addr),
                                    );
                                    let source_port = u16::to_be(val.sin_port);

                                    let parsed_addr = std::net::SocketAddr::V4(
                                        SocketAddrV4::new(
                                            source_addr,
                                            source_port,
                                        ),
                                    );

                                    dst_addr_override =
                                        crate::quic::router::resolve_dst_addr(
                                            &local_addr,
                                            &parsed_addr,
                                        );
                                },
                                ControlMessageOwned::Ipv6OrigDstAddr(val) => {
                                    let source_addr = std::net::Ipv6Addr::from(
                                        val.sin6_addr.s6_addr,
                                    );
                                    let source_port = u16::to_be(val.sin6_port);
                                    let source_flowinfo =
                                        u32::to_be(val.sin6_flowinfo);
                                    let source_scope =
                                        u32::to_be(val.sin6_scope_id);

                                    let parsed_addr = std::net::SocketAddr::V6(
                                        SocketAddrV6::new(
                                            source_addr,
                                            source_port,
                                            source_flowinfo,
                                            source_scope,
                                        ),
                                    );

                                    dst_addr_override =
                                        crate::quic::router::resolve_dst_addr(
                                            &local_addr,
                                            &parsed_addr,
                                        );
                                },
                                ControlMessageOwned::Ipv4PacketInfo(_) |
                                ControlMessageOwned::Ipv6PacketInfo(_) => {
                                    // We only want the destination address from
                                    // IP_RECVORIGDSTADDR, but we'll get these
                                    // messages because
                                    // we set IP_PKTINFO on the socket.
                                },
                                _ => {
                                    return Poll::Ready(
                                        Err(Errno::EINVAL.into()),
                                    );
                                },
                            };
                        }

                        return Poll::Ready(Ok(PollRecvData {
                            bytes,
                            src_addr: peer_addr,
                            dst_addr_override,
                            rx_time,
                            gro,
                            path_id: path_id as u64,
                        }));
                    },
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                        // Register interest in readability and wait
                        ready!(udp_socket.poll_recv_ready(cx))?;
                    },
                    Err(e) => return Poll::Ready(Err(e)),
                }
            }
        }
    }

    #[cfg(target_os = "linux")]
    fn poll_path_simple(
        &mut self, cx: &mut Context<'_>, path_id: usize,
    ) -> Poll<io::Result<PollRecvData>> {
        use std::task::ready;
        // Fallback implementation for non-UDP sockets on Linux
        let (ref mut rx, _) = self.path_rxs[path_id];
        let mut buf = tokio::io::ReadBuf::new(&mut self.buffers[path_id]);
        let addr = ready!(rx.poll_recv_from(cx, &mut buf))?;
        Poll::Ready(Ok(PollRecvData {
            bytes: buf.filled().len(),
            src_addr: addr,
            rx_time: None,
            gro: None,
            dst_addr_override: None,
            path_id: path_id as u64,
        }))
    }

    /// Process connection map commands
    fn handle_conn_map_commands(&mut self) {
        while let Ok(req) = self.conn_map_cmd_rx.try_recv() {
            match req {
                ConnectionMapCommand::UnmapCid(cid) => self.conns.unmap_cid(&cid),
                ConnectionMapCommand::RemoveScid(scid) =>
                    self.conns.remove(&scid),
                ConnectionMapCommand::MapCid(scid, id) => {
                    self.conns.map_cid_with_id(scid, id);
                },
            }
        }
    }
}

impl<Tx, Rx, M, I> Future for MultiPathInboundRouter<Tx, Rx, M, I>
where
    Tx: DatagramSocketSend + Send + 'static,
    Rx: DatagramSocketRecv + Unpin,
    M: Metrics,
    I: InitialPacketHandler + Unpin,
{
    type Output = io::Result<()>;

    fn poll(
        mut self: Pin<&mut Self>, cx: &mut Context<'_>,
    ) -> Poll<io::Result<()>> {
        loop {
            // Update the InitialPacketHandler
            if let Err(error) = self.incoming_packet_handler.update(cx) {
                // This is so rare that it's easier to spawn a separate task
                let sender = self.accept_sink.clone();
                spawn_with_killswitch(async move {
                    let _ = sender.send(Err(error)).await;
                });
            }

            // Check for shutdown conditions
            if self.shutdown_tx.is_some() && self.accept_sink.is_closed() {
                self.shutdown_tx = None;
            }

            if self.shutdown_rx.poll_recv(cx).is_ready() {
                return Poll::Ready(Ok(()));
            }

            // Process connection map commands
            self.handle_conn_map_commands();

            // Track if any path has data ready
            let mut all_pending = true;
            let mut path_with_data = None;

            // First, poll all paths to register interest with the runtime
            for path_id in 0..self.path_rxs.len() {
                match self.poll_path(cx, path_id) {
                    Poll::Ready(Ok(data)) if data.bytes > 0 => {
                        // Found data on this path
                        all_pending = false;
                        path_with_data = Some((path_id, data));
                        break; // Process one packet at a time
                    },
                    Poll::Ready(Err(e)) => return Poll::Ready(Err(e)),
                    _ => continue, // Either Pending or Ok with zero bytes
                }
            }

            // If we found data on any path, process it
            if let Some((path_id, data)) = path_with_data {
                let mut buf = std::mem::replace(
                    &mut self.buffers[path_id],
                    BufFactory::get_max_buf(),
                );
                buf.truncate(data.bytes);

                let send_from = if let Some(dst_addr) = data.dst_addr_override {
                    dst_addr
                } else {
                    self.path_rxs[path_id].1 // local address for this path
                };

                let incoming = Incoming {
                    peer_addr: data.src_addr,
                    local_addr: send_from,
                    buf,
                    rx_time: data.rx_time,
                    gro: data.gro,
                    path_id: data.path_id,
                };

                if let Err(e) = self.on_incoming(incoming) {
                    let err_type = initial_packet_error_type(&e);
                    self.metrics
                        .rejected_initial_packet_count(err_type.clone())
                        .inc();

                    if self.config.enable_expensive_packet_count_metrics {
                        if let Some(peer_ip) =
                            quic_expensive_metrics_ip_reduce(data.src_addr.ip())
                        {
                            self.metrics
                                .expensive_rejected_initial_packet_count(
                                    err_type.clone(),
                                    peer_ip,
                                )
                                .inc();
                        }
                    }

                    if matches!(
                        err_type,
                        labels::QuicInvalidInitialPacketError::Unexpected
                    ) {
                        // Don't block packet routing on errors
                        let _ = self.accept_sink.try_send(Err(e));
                    }
                }
            }

            // If all paths are pending or had zero bytes, return Pending
            if all_pending {
                return Poll::Pending;
            }
        }
    }
}
