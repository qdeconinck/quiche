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

use crate::fixtures::multipath::*;
use std::time::Duration;

#[tokio::test]
async fn test_multipath_single_socket() {
    let initial_max_path_id = 0;
    let (url, _hook) = start_multipath_server(initial_max_path_id);
    let server_addr = parse_server_addr(&url);

    // Set up client with single path
    let client_addrs = default_multipath_addrs(1);
    let (mut controller, actual_addrs) = setup_multipath_client_with_addrs(
        client_addrs,
        server_addr,
        initial_max_path_id,
    )
    .await
    .unwrap();

    assert_eq!(actual_addrs.len(), 1, "Should have 1 client address");

    // Send HTTP request and wait for response (no path probing needed for single
    // socket)
    send_multipath_http_request(&mut controller, "/")
        .await
        .unwrap();
    let success = wait_for_http_response(&mut controller, 5).await.unwrap();

    assert!(
        success,
        "Should complete HTTP request/response over single socket"
    );
}

#[tokio::test]
async fn test_multipath_multiple_sockets() {
    let initial_max_path_id = 1;
    let (url, _hook) = start_multipath_server(initial_max_path_id);
    let server_addr = parse_server_addr(&url);

    // Set up client with 2 paths
    let client_addrs = default_multipath_addrs(2);
    let (mut controller, actual_addrs) = setup_multipath_client_with_addrs(
        client_addrs,
        server_addr,
        initial_max_path_id,
    )
    .await
    .unwrap();

    assert_eq!(actual_addrs.len(), 2, "Should have 2 client addresses");

    // Probe additional paths
    probe_additional_paths(
        &mut controller,
        &actual_addrs,
        server_addr,
        Duration::from_secs(3),
    )
    .await
    .unwrap();

    // Send HTTP request and wait for response
    send_multipath_http_request(&mut controller, "/multipath-test")
        .await
        .unwrap();
    let success = wait_for_http_response(&mut controller, 5).await.unwrap();

    assert!(
        success,
        "Should complete HTTP request/response over multipath connection"
    );
}
