use clap::Parser;
use futures::SinkExt as _;
use futures::StreamExt as _;
use log::error;
use log::info;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::fs;
use tokio::io::AsyncReadExt;
use tokio_quiche::buf_factory::BufFactory;
use tokio_quiche::http3::driver::H3Event;
use tokio_quiche::http3::driver::IncomingH3Headers;
use tokio_quiche::http3::driver::OutboundFrame;
use tokio_quiche::http3::driver::OutboundFrameSender;
use tokio_quiche::http3::driver::ServerH3Event;
use tokio_quiche::http3::settings::Http3Settings;
use tokio_quiche::listen;
use tokio_quiche::metrics::DefaultMetrics;
use tokio_quiche::quic::SimpleConnectionIdGenerator;
use tokio_quiche::quiche::h3;
use tokio_quiche::quiche::h3::NameValue;
use tokio_quiche::ConnectionParams;
use tokio_quiche::ServerH3Controller;
use tokio_quiche::ServerH3Driver;

#[derive(Parser)]
#[command(name = "http3-server")]
#[command(about = "HTTP/3 server with multipath support")]
struct Args {
    /// Root directory to serve files from
    #[arg(default_value = ".")]
    root_dir: String,

    /// Enable multipath by setting initial max path ID (0 or higher enables
    /// multipath)
    #[arg(long = "initial-max-path-id")]
    initial_max_path_id: Option<u64>,

    /// Path to TLS certificate file
    #[arg(
        short = 'c',
        long = "cert",
        default_value = "tokio-quiche/examples/cert.pem"
    )]
    cert_path: String,

    /// Path to TLS private key file
    #[arg(
        short = 'k',
        long = "key",
        default_value = "tokio-quiche/examples/key.pem"
    )]
    key_path: String,

    /// Address to bind to
    #[arg(short = 'l', long = "listen", default_value = "0.0.0.0:4433")]
    listen_addr: String,

    /// Packet Scheduler to use (set one if you want to enable multipath)
    #[arg(long = "packet-scheduler", default_value = "None")]
    packet_scheduler: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::builder()
        .filter_level(log::LevelFilter::Info)
        .init();

    let args = Args::parse();

    let root_dir = PathBuf::from(&args.root_dir);
    if !root_dir.exists() || !root_dir.is_dir() {
        eprintln!(
            "Error: Root directory '{}' does not exist or is not a directory",
            root_dir.display()
        );
        std::process::exit(1);
    }

    let root_dir = Arc::new(root_dir.canonicalize()?);
    info!("Serving files from: {}", root_dir.display());

    info!("Starting HTTP/3 server on {}", args.listen_addr);
    info!("Using cert: {}", args.cert_path);
    info!("Using key: {}", args.key_path);

    let socket = tokio::net::UdpSocket::bind(&args.listen_addr).await?;

    let mut quic_params =
        ConnectionParams::default().with_packet_scheduler(&args.packet_scheduler);
    info!("Using packet scheduler: {:?}", quic_params.packet_scheduler);

    if let Some(max_path_id) = args.initial_max_path_id {
        info!("Multipath enabled with initial_max_path_id: {max_path_id}");
        quic_params.settings.initial_max_path_id = Some(max_path_id);
    }

    let mut listeners = listen(
        [socket],
        ConnectionParams::new_server(
            quic_params.settings,
            tokio_quiche::settings::TlsCertificatePaths {
                cert: &args.cert_path,
                private_key: &args.key_path,
                kind: tokio_quiche::settings::CertificateKind::X509,
            },
            Default::default(),
            quic_params.packet_scheduler,
        ),
        SimpleConnectionIdGenerator,
        DefaultMetrics,
    )?;

    let accept_stream = &mut listeners[0];

    while let Some(conn) = accept_stream.next().await {
        match conn {
            Ok(new_conn) => {
                info!("New connection from: {}", new_conn.peer_addr());
                let (driver, controller) =
                    ServerH3Driver::new(Http3Settings::default());
                new_conn.start(driver);
                tokio::spawn(handle_connection(controller, root_dir.clone()));
            },
            Err(e) => {
                error!("Failed to accept connection: {e}");
            },
        }
    }

    Ok(())
}

async fn handle_connection(
    mut controller: ServerH3Controller, root_dir: Arc<PathBuf>,
) {
    info!("Handling new HTTP/3 connection");

    while let Some(ServerH3Event::Core(event)) =
        controller.event_receiver_mut().recv().await
    {
        match event {
            H3Event::IncomingHeaders(IncomingH3Headers {
                stream_id,
                send,
                headers,
                ..
            }) => {
                info!("Received headers on stream {stream_id}: {headers:?}");

                let path = headers
                    .iter()
                    .find(|h| h.name() == b":path")
                    .map(|h| String::from_utf8_lossy(h.value()))
                    .unwrap_or_default();

                let method = headers
                    .iter()
                    .find(|h| h.name() == b":method")
                    .map(|h| String::from_utf8_lossy(h.value()))
                    .unwrap_or_default();

                info!("Request: {method} {path}");

                if method != "GET" {
                    send_error_response(send, 405, "Method Not Allowed").await;
                    continue;
                }

                let file_path = match sanitize_path(&path, &root_dir) {
                    Some(p) => p,
                    None => {
                        send_error_response(send, 400, "Invalid path").await;
                        continue;
                    },
                };

                match serve_file(send, &file_path).await {
                    Ok(_) =>
                        info!("Successfully served: {}", file_path.display()),
                    Err(e) => error!("Failed to serve file: {e}"),
                }
            },
            H3Event::BodyBytesReceived {
                stream_id,
                num_bytes,
                fin,
            } => {
                info!(
                    "Received {num_bytes} bytes on stream {stream_id} (fin={fin})"
                );
            },
            H3Event::StreamClosed { stream_id } => {
                info!("Stream {stream_id} closed");
            },
            event => {
                info!("Received event: {event:?}");
            },
        }
    }

    info!("Connection handler finished");
}

fn sanitize_path(path: &str, root_dir: &Path) -> Option<PathBuf> {
    let path = path.trim_start_matches('/');

    if path.is_empty() || path == "." {
        return Some(root_dir.to_path_buf());
    }

    let path = Path::new(path);

    for component in path.components() {
        match component {
            std::path::Component::Normal(_) => {},
            _ => return None,
        }
    }

    let full_path = root_dir.join(path);

    match full_path.canonicalize() {
        Ok(canonical) =>
            if canonical.starts_with(root_dir) {
                Some(canonical)
            } else {
                None
            },
        Err(_) => Some(full_path),
    }
}

async fn serve_file(
    mut send: OutboundFrameSender, path: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let metadata = match fs::metadata(path).await {
        Ok(m) => m,
        Err(_) => {
            send_error_response(send, 404, "Not Found").await;
            return Ok(());
        },
    };

    if !metadata.is_dir() {
        let mut file = fs::File::open(path).await?;
        let mut contents = Vec::new();
        file.read_to_end(&mut contents).await?;

        send.send(OutboundFrame::Headers(vec![h3::Header::new(
            b":status", b"200",
        )]))
        .await?;

        send.send(OutboundFrame::body(
            BufFactory::buf_from_slice(&contents),
            true,
        ))
        .await?;
    } else {
        send_error_response(send, 404, "Cannot serve directories").await;
    }

    Ok(())
}

async fn send_error_response(
    mut send: OutboundFrameSender, status_code: u16, message: &str,
) {
    let status = status_code.to_string();
    if let Err(e) = send
        .send(OutboundFrame::Headers(vec![
            h3::Header::new(b":status", status.as_bytes()),
            h3::Header::new(b"content-type", b"text/plain; charset=utf-8"),
        ]))
        .await
    {
        error!("Failed to send error headers: {e}");
        return;
    }

    if let Err(e) = send
        .send(OutboundFrame::body(
            BufFactory::buf_from_slice(message.as_bytes()),
            true,
        ))
        .await
    {
        error!("Failed to send error body: {e}");
    }
}
