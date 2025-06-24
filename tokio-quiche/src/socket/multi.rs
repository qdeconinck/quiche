use std::net::SocketAddr;
use std::sync::Arc;
use tokio::net::UdpSocket;

use super::Socket;

#[derive(Debug, Clone)]
pub struct MultiSocket<Tx, Rx> {
    pub paths: Arc<Vec<Socket<Tx, Rx>>>,
    pub peer_addr: SocketAddr,
}

impl<Tx, Rx> MultiSocket<Tx, Rx> {
    pub fn new(paths: Vec<Socket<Tx, Rx>>) -> std::io::Result<Self> {
        if paths.is_empty() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "Must provide at least one socket path",
            ));
        }

        let first_peer = paths[0].peer_addr;
        if !paths.iter().all(|p| p.peer_addr == first_peer) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "All socket paths must have the same peer address",
            ));
        }

        Ok(Self {
            paths: Arc::new(paths),
            peer_addr: first_peer,
        })
    }

    pub fn primary_path(&self) -> Option<&Socket<Tx, Rx>> {
        self.paths.first()
    }

    pub fn peer_addr(&self) -> SocketAddr {
        self.primary_path()
            .map(|p| p.peer_addr)
            .unwrap_or_else(|| self.paths[0].peer_addr)
    }

    pub fn primary_local_addr(&self) -> SocketAddr {
        self.primary_path()
            .map(|p| p.local_addr)
            .unwrap_or_else(|| self.paths[0].local_addr)
    }

    pub fn local_addrs(&self) -> Vec<SocketAddr> {
        self.paths.iter().map(|p| p.local_addr).collect()
    }

    // Find a socket based on its local address
    // Note: Finding Tx/Rx might be tricky if they aren't Arc<UdpSocket>
    pub fn find_socket_by_local_addr(
        &self, local_addr: SocketAddr,
    ) -> Option<&Socket<Tx, Rx>> {
        self.paths.iter().find(|p| p.local_addr == local_addr)
    }

    pub fn senders(&self) -> Arc<Vec<Tx>>
    where
        Tx: Clone,
    {
        Arc::new(
            self.paths
                .iter()
                .map(|socket| socket.send.clone())
                .collect(),
        )
    }
}

impl MultiSocket<Arc<UdpSocket>, Arc<UdpSocket>> {
    // If needed, provide access to all underlying sockets for reading
    // Returns a Vec of clones of the Arc<UdpSocket> used for receiving.
    pub fn all_recv_sockets(&self) -> Vec<Arc<UdpSocket>> {
        self.paths.iter().map(|p| p.recv.clone()).collect()
    }

    // Provide access to individual send sockets by local address
    // Returns a clone of the Arc<UdpSocket> used for sending on that path.
    pub fn get_send_socket(
        &self, local_addr: SocketAddr,
    ) -> Option<Arc<UdpSocket>> {
        self.paths
            .iter()
            .find(|p| p.local_addr == local_addr)
            .map(|p| p.send.clone())
    }
}
