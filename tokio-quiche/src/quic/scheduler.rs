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

use rand::seq::SliceRandom;
use rand::thread_rng;
use std::fmt::Debug;
use std::net::SocketAddr;
use std::str::FromStr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::Arc;

use crate::quic::QuicheConnection;

pub type BoxedScheduler = Arc<dyn PacketScheduler + Send + Sync + 'static>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum PacketSchedulingAlgorithm {
    /// MinRTT Path Scheduler algorithm - selects path with lowest RTT
    MinRTT        = 0,
    /// Round Robin Path Scheduler algorithm - cycles through available paths
    RoundRobin    = 1,
    /// Random Path Scheduler algorithm - randomly selects among available paths
    Random        = 2,
    /// Lowest Latency Path Scheduler algorithm - like MinRTT but also considers
    /// jitter
    LowestLatency = 3,
}

impl PacketSchedulingAlgorithm {
    /// Returns the name of the algorithm.
    pub fn name(self) -> &'static str {
        match self {
            PacketSchedulingAlgorithm::MinRTT => "minrtt",
            PacketSchedulingAlgorithm::RoundRobin => "roundrobin",
            PacketSchedulingAlgorithm::Random => "random",
            PacketSchedulingAlgorithm::LowestLatency => "lowestlatency",
        }
    }

    fn active_paths(&self, conn: &QuicheConnection) -> Vec<quiche::PathStats> {
        conn.path_stats()
            .filter(|p| {
                p.active && !matches!(p.state, quiche::PathState::Closed(_))
            })
            .collect()
    }
}

impl FromStr for PacketSchedulingAlgorithm {
    type Err = quiche::Error;

    /// Converts a string to `PacketSchedulingAlgorithm`.
    ///
    /// If `name` is not valid, `Error::PacketScheduler` is returned.
    fn from_str(name: &str) -> Result<Self, quiche::Error> {
        match name {
            "minrtt" => Ok(PacketSchedulingAlgorithm::MinRTT),
            "roundrobin" => Ok(PacketSchedulingAlgorithm::RoundRobin),
            "random" => Ok(PacketSchedulingAlgorithm::Random),
            "lowestlatency" => Ok(PacketSchedulingAlgorithm::LowestLatency),
            _ => Err(quiche::Error::UnknownPacketScheduler),
        }
    }
}

/// Trait defining a packet scheduler that can determine which path to use for
/// sending packets
pub trait PacketScheduler: Debug + Send + Sync + 'static {
    /// Get the next path to send a packet on
    fn next_path(
        &self, conn: &QuicheConnection,
    ) -> Option<(SocketAddr, SocketAddr)>;

    /// Returns the name of the scheduler.
    fn name(&self) -> &'static str;

    /// Returns the algorithm used by the scheduler.
    fn algorithm(&self) -> PacketSchedulingAlgorithm;
}

/// Factory for creating scheduler instances
pub struct PacketSchedulerFactory;

impl PacketSchedulerFactory {
    /// Create a new scheduler instance based on the algorithm
    pub fn create(algorithm: PacketSchedulingAlgorithm) -> BoxedScheduler {
        match algorithm {
            PacketSchedulingAlgorithm::MinRTT => Arc::new(MinRTTScheduler::new()),
            PacketSchedulingAlgorithm::RoundRobin =>
                Arc::new(RoundRobinScheduler::new()),
            PacketSchedulingAlgorithm::Random => Arc::new(RandomScheduler::new()),
            PacketSchedulingAlgorithm::LowestLatency =>
                Arc::new(LowestLatencyScheduler::new()),
        }
    }

    /// Create a new scheduler instance from a string name
    pub fn from_name(name: &str) -> Result<BoxedScheduler, quiche::Error> {
        let algorithm = PacketSchedulingAlgorithm::from_str(name)?;
        Ok(Self::create(algorithm))
    }
}

/// MinRTT Path Scheduler algorithm.
#[derive(Debug, Clone)]
pub struct MinRTTScheduler;

impl MinRTTScheduler {
    pub fn new() -> Self {
        Self
    }
}

impl Default for MinRTTScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl PacketScheduler for MinRTTScheduler {
    fn next_path(
        &self, conn: &QuicheConnection,
    ) -> Option<(SocketAddr, SocketAddr)> {
        if let Some((path_id, _)) = conn.get_next_send_path_id(None, None, None) {
            let path = conn.path_stats().find(|p| p.path_id == path_id);
            if let Some(path) = path {
                return Some((path.local_addr, path.peer_addr));
            }
        }

        let mut paths = self.algorithm().active_paths(conn);

        if paths.is_empty() {
            return None;
        }

        // Sort paths by RTT (lowest first)
        paths.sort_by(|a, b| a.rtt.cmp(&b.rtt));
        // eprintln!("Sorted paths: {:?}", paths);

        // Return the path with the lowest RTT
        paths.first().map(|p| (p.local_addr, p.peer_addr))
    }

    fn name(&self) -> &'static str {
        self.algorithm().name()
    }

    fn algorithm(&self) -> PacketSchedulingAlgorithm {
        PacketSchedulingAlgorithm::MinRTT
    }
}

/// Round Robin Path Scheduler algorithm.
#[derive(Debug)]
pub struct RoundRobinScheduler {
    current_index: AtomicUsize,
}

impl RoundRobinScheduler {
    pub fn new() -> Self {
        Self {
            current_index: 0.into(),
        }
    }
}

impl Default for RoundRobinScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl PacketScheduler for RoundRobinScheduler {
    fn next_path(
        &self, conn: &QuicheConnection,
    ) -> Option<(SocketAddr, SocketAddr)> {
        if let Some((path_id, _)) = conn.get_next_send_path_id(None, None, None) {
            let path = conn.path_stats().find(|p| p.path_id == path_id);
            if let Some(path) = path {
                return Some((path.local_addr, path.peer_addr));
            }
        }

        let idx = self.current_index.fetch_add(1, Relaxed);
        let paths = self.algorithm().active_paths(conn);

        if paths.is_empty() {
            return None;
        }

        // Get the next path in round-robin fashion
        let path = &paths[idx % paths.len()];

        // Update the index for the next call
        self.current_index.store((idx + 1) % paths.len(), Relaxed);

        Some((path.local_addr, path.peer_addr))
    }

    fn name(&self) -> &'static str {
        self.algorithm().name()
    }

    fn algorithm(&self) -> PacketSchedulingAlgorithm {
        PacketSchedulingAlgorithm::RoundRobin
    }
}

/// Random Path Scheduler algorithm.
#[derive(Debug)]
pub struct RandomScheduler;

impl RandomScheduler {
    pub fn new() -> Self {
        Self
    }
}

impl Default for RandomScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl PacketScheduler for RandomScheduler {
    fn next_path(
        &self, conn: &QuicheConnection,
    ) -> Option<(SocketAddr, SocketAddr)> {
        if let Some((path_id, _)) = conn.get_next_send_path_id(None, None, None) {
            let path = conn.path_stats().find(|p| p.path_id == path_id);
            if let Some(path) = path {
                return Some((path.local_addr, path.peer_addr));
            }
        }

        let paths = self.algorithm().active_paths(conn);

        if paths.is_empty() {
            return None;
        }

        // Randomly select an active path
        let mut rng = thread_rng();
        paths.choose(&mut rng).map(|p| (p.local_addr, p.peer_addr))
    }

    fn name(&self) -> &'static str {
        self.algorithm().name()
    }

    fn algorithm(&self) -> PacketSchedulingAlgorithm {
        PacketSchedulingAlgorithm::Random
    }
}

/// Lowest Latency Path Scheduler algorithm.
#[derive(Debug)]
pub struct LowestLatencyScheduler;

impl LowestLatencyScheduler {
    pub fn new() -> Self {
        Self
    }
}

impl Default for LowestLatencyScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl PacketScheduler for LowestLatencyScheduler {
    fn next_path(
        &self, conn: &QuicheConnection,
    ) -> Option<(SocketAddr, SocketAddr)> {
        let mut paths = self.algorithm().active_paths(conn);

        if paths.is_empty() {
            return None;
        }

        // Sort paths by a combination of RTT and RTT variance
        // This is a simple weighted formula that considers both metrics:
        // score = rtt + (2 * rttvar)
        paths.sort_by(|a, b| {
            let a_score = a.rtt + (a.rttvar * 2);
            let b_score = b.rtt + (b.rttvar * 2);
            a_score.cmp(&b_score)
        });

        // Return the path with the lowest latency score
        paths.first().map(|p| (p.local_addr, p.peer_addr))
    }

    fn name(&self) -> &'static str {
        self.algorithm().name()
    }

    fn algorithm(&self) -> PacketSchedulingAlgorithm {
        PacketSchedulingAlgorithm::LowestLatency
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scheduler_factory_create() {
        let scheduler =
            PacketSchedulerFactory::create(PacketSchedulingAlgorithm::MinRTT);
        assert_eq!(scheduler.algorithm(), PacketSchedulingAlgorithm::MinRTT);
        assert_eq!(scheduler.name(), "minrtt");

        let scheduler =
            PacketSchedulerFactory::create(PacketSchedulingAlgorithm::RoundRobin);
        assert_eq!(scheduler.algorithm(), PacketSchedulingAlgorithm::RoundRobin);
        assert_eq!(scheduler.name(), "roundrobin");

        let scheduler =
            PacketSchedulerFactory::create(PacketSchedulingAlgorithm::Random);
        assert_eq!(scheduler.algorithm(), PacketSchedulingAlgorithm::Random);
        assert_eq!(scheduler.name(), "random");

        let scheduler = PacketSchedulerFactory::create(
            PacketSchedulingAlgorithm::LowestLatency,
        );
        assert_eq!(
            scheduler.algorithm(),
            PacketSchedulingAlgorithm::LowestLatency
        );
        assert_eq!(scheduler.name(), "lowestlatency");
    }

    #[test]
    fn test_round_robin_index_cycling() {
        let scheduler = RoundRobinScheduler::new();

        // Test that the internal index starts at 0
        assert_eq!(scheduler.current_index.load(Relaxed), 0);

        // Test that fetch_add increments the index
        let idx1 = scheduler.current_index.fetch_add(1, Relaxed);
        assert_eq!(idx1, 0);
        assert_eq!(scheduler.current_index.load(Relaxed), 1);

        let idx2 = scheduler.current_index.fetch_add(1, Relaxed);
        assert_eq!(idx2, 1);
        assert_eq!(scheduler.current_index.load(Relaxed), 2);
    }
}
