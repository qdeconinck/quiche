use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;
use tokio::net::UdpSocket;

use clap::Parser;
use log::info;
use log::warn;
use tokio_quiche::http3::driver::ClientH3Event;
use tokio_quiche::http3::driver::H3Event;
use tokio_quiche::http3::driver::InboundFrame;
use tokio_quiche::http3::driver::IncomingH3Headers;
use tokio_quiche::http3::settings::Http3Settings;
use tokio_quiche::quiche::h3;
use tokio_quiche::socket::MultiSocket;
use tokio_quiche::socket::Socket;
use tokio_quiche::ClientH3Driver;

use tokio_quiche::ConnectionParams;
use url::Url;

#[derive(Parser)]
#[command(name = "http3-client")]
#[command(about = "HTTP/3 client with multipath support")]
struct Args {
    /// URL to request
    #[arg(default_value = "https://127.0.0.1:4433/")]
    url: String,

    /// Enable multipath functionality
    #[arg(short = 'm', long = "multipath")]
    multipath: bool,

    /// Local address(es) to use (can be specified multiple times for multipath)
    #[arg(short = 'A', long = "address", action = clap::ArgAction::Append)]
    addresses: Vec<SocketAddr>,

    /// Timeout for path probing in seconds
    #[arg(long = "probe-timeout", default_value = "5")]
    probe_timeout: u64,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::builder()
        .filter_level(log::LevelFilter::Info)
        .init();

    let args = Args::parse();

    let url = Url::parse(&args.url)?;

    let scheme = url.scheme();
    let host = url.host_str().ok_or("Invalid host in URL")?;
    let port = url.port().unwrap_or(match scheme {
        "https" => 443,
        "http" => 80,
        _ => return Err(format!("Unsupported scheme: {}", scheme).into()),
    });
    let path = url.path();

    info!("Requesting URL: {}", args.url);
    info!(
        "Parsed - scheme: {}, host: {}, port: {}, path: {}",
        scheme, host, port, path
    );

    let mut params = ConnectionParams::default();
    params.settings.max_idle_timeout = Some(Duration::from_secs(30));

    if args.multipath {
        let addrs = args.addresses.len();
        info!("Multipath enabled with {} additional addresses", addrs);

        params.settings.initial_max_path_id = Some(addrs as u64);
    }

    let server_addr: SocketAddr = format!("{}:{}", host, port).parse()?;
    let mut sockets: Vec<Socket<Arc<UdpSocket>, Arc<UdpSocket>>> = Vec::new();
    for addr in &args.addresses {
        let udp_socket = UdpSocket::bind(addr).await?;
        // Connect to remote
        udp_socket.connect(&server_addr).await?;
        let socket = Socket::<UdpSocket, UdpSocket>::from_udp(udp_socket)?;
        sockets.push(socket);
    }

    if sockets.is_empty() {
        return Err("No valid local addresses provided".into());
    }

    info!(
        "Connecting to {} from {}",
        server_addr,
        args.addresses
            .iter()
            .map(|a| a.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );

    let multi_socket = MultiSocket::new(sockets)?;
    let (driver, mut controller) = ClientH3Driver::new(Http3Settings::default());
    let _ = tokio_quiche::quic::connect_with_config(
        multi_socket,
        Some(host),
        &params,
        driver,
    )
    .await
    .map_err(|e| format!("Failed to connect: {}", e))?;

    info!("Connected! QUIC connection established");

    // If multipath is enabled, probe additional paths before sending HTTP
    // requests
    let add_addresses = &args.addresses[1..];
    if args.multipath && !add_addresses.is_empty() {
        info!("Probing {} additional paths...", add_addresses.len());

        let probes_pending = add_addresses.len();
        let probe_timeout = Duration::from_secs(args.probe_timeout);

        // Start probing all additional addresses
        for &addr in add_addresses {
            info!("Probing path from {} to {}", addr, server_addr);
            controller
                .cmd_sender()
                .send(tokio_quiche::quic::QuicCommand::OpenPath(
                    None,
                    addr,
                    server_addr,
                ))
                .ok();
        }

        // Wait for probe results with timeout
        let probe_start = tokio::time::Instant::now();
        while probes_pending > 0 && probe_start.elapsed() < probe_timeout {
            tokio::select! {
                _event_opt = controller.event_receiver_mut().recv() => {
                    // if let Some(event) = event_opt {
                    //     match event {
                    //     }
                    // } else {
                    //     break;
                    // }
                },
                _ = tokio::time::sleep(Duration::from_millis(100)) => {
                    // Continue waiting
                }
            }
        }

        if probes_pending > 0 {
            warn!("{} path probes timed out", probes_pending);
        }

        info!("Path probing completed, proceeding with HTTP request");
    }

    info!("Sending HTTP/3 request");

    controller
        .request_sender()
        .send(tokio_quiche::http3::driver::NewClientRequest {
            request_id: 0,
            headers: vec![
                h3::Header::new(b":method", b"GET"),
                h3::Header::new(b":scheme", scheme.as_bytes()),
                h3::Header::new(b":authority", host.as_bytes()),
                h3::Header::new(b":path", path.as_bytes()),
            ],
            body_writer: None,
        })
        .unwrap();

    // Main event loop for HTTP/3 request/response
    while let Some(event) = controller.event_receiver_mut().recv().await {
        match event {
            ClientH3Event::Core(H3Event::IncomingHeaders(
                IncomingH3Headers {
                    stream_id,
                    headers,
                    mut recv,
                    ..
                },
            )) => {
                info!("Received headers on stream {}: {:?}", stream_id, headers);

                let mut response_body = Vec::new();

                'body: while let Some(frame) = recv.recv().await {
                    match frame {
                        InboundFrame::Body(pooled, fin) => {
                            response_body.extend_from_slice(&pooled);

                            if fin {
                                println!(
                                    "{}",
                                    String::from_utf8_lossy(&response_body)
                                );

                                info!(
                                    "Received full response body ({} bytes)",
                                    response_body.len()
                                );
                                break 'body;
                            }
                        },
                        InboundFrame::Datagram(pooled) => {
                            info!("Received datagram: {} bytes", pooled.len());
                        },
                    }
                }
            },
            ClientH3Event::Core(H3Event::BodyBytesReceived {
                fin: true, ..
            }) => {
                info!("Finished receiving response");
                // Send connection close command
                controller
                    .cmd_sender()
                    .send(tokio_quiche::quic::QuicCommand::ConnectionClose(
                        tokio_quiche::quic::ConnectionShutdownBehaviour {
                            send_application_close: false,
                            error_code: 0,
                            reason: Vec::new(),
                        },
                    ))
                    .ok();
                break;
            },
            ClientH3Event::Core(event) => {
                info!("Received event: {:?}", event);
            },
            ClientH3Event::NewOutboundRequest {
                stream_id,
                request_id,
            } => {
                info!(
                    "Sending outbound request - stream_id: {}, request_id: {}",
                    stream_id, request_id
                );
            },
        }
    }

    info!("Client shutting down");
    Ok(())
}
