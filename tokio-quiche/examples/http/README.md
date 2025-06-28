# HTTP/3 Example with MPQUIC Support

This example demonstrates how to use tokio-quiche to build HTTP/3 client and server applications with MPQUIC (Multipath
QUIC) support.

## Prerequisites

The server requires TLS certificates. By default, it looks for them in the parent directory:

- `../cert.pem` - TLS certificate
- `../key.pem` - TLS private key

## Building

From the `tokio-quiche/examples/http` directory:

```bash
cargo build
```

## Running the Server

### Basic Usage

```bash
cargo run --bin http3-server
```

The server will listen on `0.0.0.0:4433` and serve files from the current directory.

### Server Options

```bash
cargo run --bin http3-server -- --help
```

- `<ROOT_DIR>`: Directory to serve files from (default: current directory)
- `--cert <PATH>`: Path to TLS certificate (default: `../cert.pem`)
- `--key <PATH>`: Path to TLS private key (default: `../key.pem`)
- `-l, --listen <ADDR>`: Address to bind to (default: `0.0.0.0:4433`)
- `--initial-max-path-id <ID>`: Enable multipath with specified max path ID
- `--packet-scheduler <SCHEDULER>`: Packet scheduler for multipath (default: `None`)

Think of attributing a packet scheduler if you enable multipath. Available options are:

- `None`: No packet scheduling
- `minrtt`: Minimum RTT scheduling
- `roundrobin`: Round-robin scheduling
- `random`: Random scheduling
- `lowestlatency`: Lowest-latency scheduling

### Multipath Server Example

```bash
# Enable multipath with max 2 paths and round-robin scheduler
cargo run --bin http3-server -- --initial-max-path-id 2 --packet-scheduler RoundRobin
```

## Running the Client

### Basic Usage

```bash
cargo run --bin http3-client
```

The client will connect to `https://127.0.0.1:4433/` and display the response.

### Client Options

```bash
cargo run --bin http3-client -- --help
```

- `<URL>`: URL to request (default: `https://127.0.0.1:4433/`)
- `-m, --multipath`: Enable multipath functionality
- `-A, --address <ADDR>`: Local address to bind to (can be specified multiple times for multipath)
- `--probe-timeout <SECONDS>`: Timeout for path probing in seconds (default: 5)

### Multipath Client Examples

```bash
# Enable multipath with multiple local addresses
cargo run --bin http3-client -- -m -A 127.0.0.1:1234 -A 127.0.0.1:5678

# Request specific URL with multipath
cargo run --bin http3-client -- http://127.0.0.1:4433/test.txt -m -A 127.0.0.1:1234 -A 127.0.0.1:5678

# Multiple addresses with custom probe timeout
cargo run --bin http3-client -- -m -A 127.0.0.1:1234 -A 127.0.0.1:5678 --probe-timeout 10
```

### How Multipath Works

When multipath is enabled (`-m`), the client:

1. **Creates Multiple Sockets**: Binds to each address specified with `-A`
2. **Establishes Connection**: Uses MultiSocket to connect with all addresses
3. **Probes Paths**: Tests connectivity on each additional path
4. **Sends HTTP Request**: Proceeds with the HTTP/3 request using available paths

The first address in the `-A` list becomes the primary path / path id 0 (used during the handshake), with additional
addresses used as alternate paths.

## Implementation Notes

### Server Features

- **File Serving**: Serves static files from a specified root directory
- **Path Sanitization**: Prevents directory traversal attacks
- **Error Handling**: Returns appropriate HTTP status codes
- **Multipath Support**: Can be enabled with `--initial-max-path-id` and packet schedulers

### Client Features

- **Multi-Socket Support**: Uses `MultiSocket` for binding to multiple addresses
- **Path Probing**: Opens additional paths before sending HTTP requests
- **URL Parsing**: Supports full URL specification with scheme, host, port, and path
- **Graceful Shutdown**: Properly closes the connection after receiving response
