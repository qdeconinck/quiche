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

use futures::StreamExt;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;
use tokio::net::UdpSocket;
use tokio_quiche::http3::settings::Http3Settings;
use tokio_quiche::listen;
use tokio_quiche::metrics::DefaultMetrics;
use tokio_quiche::quic::SimpleConnectionIdGenerator;
use tokio_quiche::settings::QuicSettings;
use tokio_quiche::socket::MultiSocket;
use tokio_quiche::socket::Socket;
use tokio_quiche::ClientH3Driver;
use tokio_quiche::ConnectionParams;

use super::handle_connection;
use super::TestConnectionHook;
use super::TEST_CERT_FILE;
use super::TEST_KEY_FILE;

/// Creates default local addresses for multipath testing
pub fn default_multipath_addrs(num_paths: usize) -> Vec<SocketAddr> {
    (0..num_paths)
        .map(|_| "127.0.0.1:0".parse().unwrap())
        .collect()
}

/// Creates QuicSettings with multipath configuration  
pub fn multipath_quic_settings(max_path_id: Option<u64>) -> QuicSettings {
    QuicSettings {
        initial_max_path_id: max_path_id,
        max_idle_timeout: Some(Duration::from_secs(30)),
        ..Default::default()
    }
}

/// Starts a multipath-enabled server and returns the URL
pub fn start_multipath_server(
    max_path_id: u64,
) -> (String, Arc<TestConnectionHook>) {
    let quic_settings = multipath_quic_settings(Some(max_path_id));
    let hook = TestConnectionHook::new();

    (
        start_multipath_server_with_settings(
            quic_settings,
            Http3Settings::default(),
            None,
            hook.clone(),
            handle_connection,
        ),
        hook,
    )
}

/// Starts a multipath server with custom settings
pub fn start_multipath_server_with_settings<F, Fut>(
    quic_settings: QuicSettings, http3_settings: Http3Settings,
    packet_scheduler: Option<tokio_quiche::quic::scheduler::BoxedScheduler>,
    hook: Arc<impl tokio_quiche::quic::ConnectionHook + Send + Sync + 'static>,
    hdl: F,
) -> String
where
    F: Fn(tokio_quiche::ServerH3Connection) -> Fut + Send + Clone + 'static,
    Fut: std::future::Future<Output = ()> + Send,
{
    let socket = std::net::UdpSocket::bind("127.0.0.1:0").unwrap();
    let url = format!("http://127.0.0.1:{}", socket.local_addr().unwrap().port());

    let tls_cert_settings = tokio_quiche::settings::TlsCertificatePaths {
        cert: &TEST_CERT_FILE,
        private_key: &TEST_KEY_FILE,
        kind: tokio_quiche::settings::CertificateKind::X509,
    };

    let hooks = tokio_quiche::settings::Hooks {
        connection_hook: Some(hook),
    };

    let params = ConnectionParams::new_server(
        quic_settings,
        tls_cert_settings,
        hooks,
        packet_scheduler,
    );
    let mut stream = listen(
        vec![socket],
        params,
        SimpleConnectionIdGenerator,
        DefaultMetrics,
    )
    .unwrap()
    .remove(0);

    tokio::spawn(async move {
        loop {
            let (h3_driver, h3_controller) =
                tokio_quiche::ServerH3Driver::new(http3_settings.clone());
            let conn = stream.next().await.unwrap().unwrap().start(h3_driver);
            let h3_over_quic =
                tokio_quiche::ServerH3Connection::new(conn, h3_controller);

            let hdl = hdl.clone();
            tokio::spawn(async move {
                hdl(h3_over_quic).await;
            });
        }
    });

    url
}

/// Creates multiple UDP sockets bound to different local addresses for
/// multipath testing - returns both sockets and their actual bound addresses
pub async fn create_multipath_sockets_with_addrs(
    local_addrs: &[SocketAddr], server_addr: SocketAddr,
) -> Result<
    (Vec<Socket<Arc<UdpSocket>, Arc<UdpSocket>>>, Vec<SocketAddr>),
    Box<dyn std::error::Error>,
> {
    let mut sockets = Vec::new();
    let mut actual_addrs = Vec::new();

    for &addr in local_addrs {
        let udp_socket = UdpSocket::bind(addr).await?;
        let actual_addr = udp_socket.local_addr()?;
        udp_socket.connect(&server_addr).await?;
        let socket = Socket::<UdpSocket, UdpSocket>::from_udp(udp_socket)?;
        sockets.push(socket);
        actual_addrs.push(actual_addr);
    }

    Ok((sockets, actual_addrs))
}

/// Creates multiple UDP sockets bound to different local addresses for
/// multipath testing
pub async fn create_multipath_sockets(
    local_addrs: &[SocketAddr], server_addr: SocketAddr,
) -> Result<Vec<Socket<Arc<UdpSocket>, Arc<UdpSocket>>>, Box<dyn std::error::Error>>
{
    let (sockets, _) =
        create_multipath_sockets_with_addrs(local_addrs, server_addr).await?;
    Ok(sockets)
}

/// Creates a MultiSocket from a vector of individual sockets
pub fn create_multi_socket(
    sockets: Vec<Socket<Arc<UdpSocket>, Arc<UdpSocket>>>,
) -> Result<MultiSocket<Arc<UdpSocket>, Arc<UdpSocket>>, Box<dyn std::error::Error>>
{
    MultiSocket::new(sockets).map_err(|e| e.into())
}

/// Sets up a multipath-enabled client connection and returns controller and
/// actual addresses
pub async fn setup_multipath_client_with_addrs(
    local_addrs: Vec<SocketAddr>, server_addr: SocketAddr, max_path_id: u64,
) -> Result<
    (tokio_quiche::ClientH3Controller, Vec<SocketAddr>),
    Box<dyn std::error::Error>,
> {
    let (sockets, actual_addrs) =
        create_multipath_sockets_with_addrs(&local_addrs, server_addr).await?;
    let multi_socket = create_multi_socket(sockets)?;

    let mut client_params = ConnectionParams::default();
    client_params.settings.initial_max_path_id = Some(max_path_id);
    client_params.settings.max_idle_timeout = Some(Duration::from_secs(30));

    let (driver, controller) = ClientH3Driver::new(Http3Settings::default());
    tokio_quiche::quic::connect_with_config(
        multi_socket,
        Some("test.com"),
        &client_params,
        driver,
    )
    .await
    .map_err(|e| format!("Failed to connect: {e}"))?;

    Ok((controller, actual_addrs))
}

/// Sets up a multipath-enabled client connection and returns just the
/// controller
pub async fn setup_multipath_client(
    local_addrs: Vec<SocketAddr>, server_addr: SocketAddr, max_path_id: u64,
) -> Result<tokio_quiche::ClientH3Controller, Box<dyn std::error::Error>> {
    let (controller, _) =
        setup_multipath_client_with_addrs(local_addrs, server_addr, max_path_id)
            .await?;
    Ok(controller)
}

/// Helper to probe additional paths after connection establishment
pub async fn probe_additional_paths(
    controller: &mut tokio_quiche::ClientH3Controller,
    local_addrs: &[SocketAddr], server_addr: SocketAddr, probe_timeout: Duration,
) -> Result<(), Box<dyn std::error::Error>> {
    if local_addrs.len() <= 1 {
        return Ok(());
    }

    let additional_addrs = &local_addrs[1..];

    for &addr in additional_addrs {
        controller
            .cmd_sender()
            .send(tokio_quiche::quic::QuicCommand::OpenPath(
                None,
                addr,
                server_addr,
            ))
            .ok();
    }

    let probe_start = tokio::time::Instant::now();
    while probe_start.elapsed() < probe_timeout {
        tokio::select! {
            _event_opt = controller.event_receiver_mut().recv() => {
                // Process probe events
            },
            _ = tokio::time::sleep(Duration::from_millis(100)) => {
                // Continue waiting
            }
        }
    }

    Ok(())
}

/// Helper to parse server address from URL
pub fn parse_server_addr(url: &str) -> SocketAddr {
    url.strip_prefix("http://")
        .unwrap_or(url)
        .parse()
        .expect("Invalid server URL")
}

/// Helper to send a single HTTP request over multipath connection
pub async fn send_multipath_http_request(
    controller: &mut tokio_quiche::ClientH3Controller, path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    controller.request_sender().send(
        tokio_quiche::http3::driver::NewClientRequest {
            request_id: 0,
            headers: vec![
                tokio_quiche::quiche::h3::Header::new(b":method", b"GET"),
                tokio_quiche::quiche::h3::Header::new(b":scheme", b"https"),
                tokio_quiche::quiche::h3::Header::new(b":authority", b"test.com"),
                tokio_quiche::quiche::h3::Header::new(b":path", path.as_bytes()),
            ],
            body_writer: None,
        },
    )?;
    Ok(())
}

/// Helper to wait for HTTP response completion
pub async fn wait_for_http_response(
    controller: &mut tokio_quiche::ClientH3Controller, timeout_secs: u64,
) -> Result<bool, Box<dyn std::error::Error>> {
    let result = tokio::time::timeout(Duration::from_secs(timeout_secs), async {
        let mut got_headers = false;
        let mut body_complete = false;

        while let Some(event) = controller.event_receiver_mut().recv().await {
            match event {
                tokio_quiche::http3::driver::ClientH3Event::Core(
                    tokio_quiche::http3::driver::H3Event::IncomingHeaders(_),
                ) => {
                    got_headers = true;
                },
                tokio_quiche::http3::driver::ClientH3Event::Core(
                    tokio_quiche::http3::driver::H3Event::BodyBytesReceived {
                        fin: true,
                        ..
                    },
                ) => {
                    body_complete = true;
                },
                _ => {},
            }

            if got_headers && body_complete {
                return true;
            }
        }
        false
    })
    .await?;

    Ok(result)
}
