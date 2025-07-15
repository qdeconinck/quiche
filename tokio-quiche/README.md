# Tokio Quiche

Bridging the gap between [quiche][quiche] and [tokio][tokio].

tokio-quiche connects [quiche::Connection][q-connection]s and [quiche::h3::Connection][q-h3-connection]s to tokio's
event loop. Users have the choice between implementing their own, custom <code>[ApplicationOverQuic]</code> or using the
ready-made <code>[H3Driver]</code> for HTTP/3 clients and servers.

# Starting an HTTP/3 Server

A server listens on a UDP socket for QUIC connections and spawns a new tokio task to handle each individual connection.

```rust
use foundations::telemetry::log;
use futures::{SinkExt as _, StreamExt as _};
use tokio_quiche::buf_factory::BufFactory;
use tokio_quiche::http3::driver::{H3Event, IncomingH3Headers, OutboundFrame, ServerH3Event};
use tokio_quiche::http3::settings::Http3Settings;
use tokio_quiche::listen;
use tokio_quiche::metrics::DefaultMetrics;
use tokio_quiche::quic::SimpleConnectionIdGenerator;
use tokio_quiche::quiche::h3;
use tokio_quiche::{ConnectionParams, ServerH3Controller, ServerH3Driver};

let socket = tokio::net::UdpSocket::bind("0.0.0.0:4043").await?;
let mut listeners = listen(
    [socket],
    ConnectionParams::new_server(
        Default::default(),
        tokio_quiche::settings::TlsCertificatePaths {
            cert: "/path/to/cert.pem",
            private_key: "/path/to/key.pem",
            kind: tokio_quiche::settings::CertificateKind::X509,
        },
        Default::default(),
    ),
    SimpleConnectionIdGenerator,
    DefaultMetrics,
)?;
let accept_stream = &mut listeners[0];

while let Some(conn) = accept_stream.next().await {
    let (driver, controller) = ServerH3Driver::new(Http3Settings::default());
    conn?.start(driver);
    tokio::spawn(handle_connection(controller));
}

async fn handle_connection(mut controller: ServerH3Controller) {
    while let Some(ServerH3Event::Core(event)) = controller.event_receiver_mut().recv().await {
        match event {
            H3Event::IncomingHeaders(IncomingH3Headers {
                mut send, headers, ..
            }) => {
                log::info!("incomming headers"; "headers" => ?headers);
                send.send(OutboundFrame::Headers(vec![h3::Header::new(
                    b":status", b"200",
                )]))
                .await
                .unwrap();

                send.send(OutboundFrame::body(
                    BufFactory::buf_from_slice(b"hello from TQ!"),
                    true,
                ))
                .await
                .unwrap();
            }
            event => {
                log::info!("event: {event:?}");
            }
        }
    }
}
```

# Sending an HTTP/3 request

```rust
use foundations::telemetry::log;
use tokio_quiche::http3::driver::{ClientH3Event, H3Event, InboundFrame, IncomingH3Headers};
use tokio_quiche::quiche::h3;

let socket = tokio::net::UdpSocket::bind("0.0.0.0:0").await?;
socket.connect("127.0.0.1:4043").await?;
let (_, mut controller) = tokio_quiche::quic::connect(socket, None).await?;

controller
    .request_sender()
    .send(tokio_quiche::http3::driver::NewClientRequest {
        request_id: 0,
        headers: vec![h3::Header::new(b":method", b"GET")],
        body_writer: None,
    })
    .unwrap();

while let Some(event) = controller.event_receiver_mut().recv().await {
    match event {
        ClientH3Event::Core(H3Event::IncomingHeaders(IncomingH3Headers {
            stream_id,
            headers,
            mut recv,
            ..
        })) => {
            log::info!("incomming headers"; "stream_id" => stream_id, "headers" => ?headers);
            'body: while let Some(frame) = recv.recv().await {
                match frame {
                    InboundFrame::Body(pooled, fin) => {
                        log::info!("inbound body: {:?}", std::str::from_utf8(&pooled);
                            "fin" => fin,
                            "len" => pooled.len()
                        );
                        if fin {
                            log::info!("received full body, exiting");
                            break 'body;
                        }
                    }
                    InboundFrame::Datagram(pooled) => {
                        log::info!("inbound datagram"; "len" => pooled.len());
                    }
                }
            }
        }
        ClientH3Event::Core(H3Event::BodyBytesReceived { fin: true, .. }) => {
            log::info!("fin received");
            break;
        }
        ClientH3Event::Core(event) => log::info!("received event: {event:?}"),
        ClientH3Event::NewOutboundRequest {
            stream_id,
            request_id,
        } => log::info!(
            "sending outbound request";
            "stream_id" => stream_id,
            "request_id" => request_id
        ),
    }
}
```

**Note**: Omited in these two examples are is the use of `stream_id` to track multiplexed requests within the same
connection.

# Feature Flags

tokio-quiche supports a number of feature flags to enable experimental features, performance enhancements, and
additional telemetry. By default, no feature flags are enabled.

- `rpk`: Support for raw public keys (RPK) in QUIC handshakes (via [boring]).
- `capture_keylogs`: Optional `SSLKEYLOGFILE` capturing for QUIC connections.
- `gcongestion`: Replace quiche's original congestion control implementation with one adapted from google/quiche (via
  quiche-mallard).
- `zero-copy`: Use zero-copy sends with quiche-mallard (implies `gcongestion`).
- `perf-quic-listener-metrics`: Extra telemetry for QUIC handshake durations, including protocol overhead and network
  delays.
- `tokio-task-metrics`: Scheduling & poll duration histograms for tokio tasks.

# Multipath QUIC (MPQUIC) Support

tokio-quiche supports Multipath QUIC (MPQUIC), allowing connections to use multiple network paths simultaneously for
improved performance and reliability.

## Enabling Multipath

To enable multipath support, set the `initial_max_path_id` parameter in your QUIC settings:

```rust
use tokio_quiche::{ConnectionParams, settings::QuicSettings};

// Enable multipath with up to 2 additional paths (3 total including primary)
let mut quic_settings = QuicSettings::default();
quic_settings.initial_max_path_id = Some(2);

let params = ConnectionParams::new_server(
    quic_settings,
    tls_settings,
    http3_settings,
);
```

## Packet Schedulers

When using multipath, you can configure packet scheduling algorithms to determine how packets are distributed across
available paths:

### Available Schedulers

- **MinRTT** (`"minrtt"`): Selects the path with the lowest round-trip time
- **RoundRobin** (`"roundrobin"`): Cycles through available paths in order
- **Random** (`"random"`): Randomly selects among available paths
- **LowestLatency** (`"lowestlatency"`): Uses RTT + 2×RTT variance for path selection

### Configuration

```rust
// Using a built-in scheduler
let params = ConnectionParams::default()
    .with_packet_scheduler("minrtt");

// Using a custom scheduler implementation
let custom_scheduler = MyCustomScheduler::new();
let params = ConnectionParams::default()
    .with_custom_packet_scheduler(custom_scheduler);
```

## Examples

The `examples/http` directory contains HTTP/3 client and server examples with MPQUIC support:

### Server with Multipath

```bash
# Start server with multipath enabled (max 3 paths) using MinRTT scheduler
cargo run --bin http3-server -- --initial-max-path-id 2 --packet-scheduler minrtt .
```

### Client with Multiple Addresses

```bash
# Connect using multiple local addresses for multipath
cargo run --bin http3-client -- -m -A 127.0.0.1:1234 -A 127.0.0.1:5678 https://localhost:4433/
```

For detailed examples and configuration options, see the [HTTP/3 example app documentation](examples/http/README.md).

# Server usage architecture

![server-arch](https://github.com/cloudflare/quiche/blob/master/tokio-quiche/docs/arch-server.drawio.svg?raw=true)

# Client usage architecture

![client-arch](https://github.com/cloudflare/quiche/blob/master/tokio-quiche/docs/arch-client.drawio.svg?raw=true)

[quiche]: https://docs.quic.tech/quiche/
[tokio]: https://tokio.rs
[q-connection]: https://docs.quic.tech/quiche/struct.Connection.html
[q-h3-connection]: https://docs.quic.tech/quiche/h3/struct.Connection.html
[connect]: https://docs.rs/tokio-quiche/latest/tokio_quiche/quic/fn.connect.html
[ApplicationOverQuic]: https://docs.rs/tokio-quiche/latest/tokio_quiche/trait.ApplicationOverQuic.html
[H3Driver]: https://docs.rs/tokio-quiche/latest/tokio-quiche/http3/driver/struct.H3Driver.html
