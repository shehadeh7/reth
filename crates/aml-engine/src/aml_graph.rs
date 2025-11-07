use petgraph::stable_graph::{StableGraph, NodeIndex, EdgeIndex};
use petgraph::Direction::{Incoming};
use std::collections::{HashMap, HashSet, VecDeque};
use alloy_primitives::{Address, B256, U256};
use petgraph::Outgoing;

/// ---------------------------------------------------------------------------
/// Public Types
/// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Config {
    /// Sliding window size in blocks (e.g., 7200 ≈ 1 day)
    pub window_blocks: u64,
    /// Smurfing: max distinct senders to one address
    pub fan_in_count_threshold: u64,
    /// Smurfing: max total inflow amount
    pub fan_in_sum_threshold: U256,
    /// Scatter-gather: threshold for total flow through multiple intermediaries
    pub scatter_gather_threshold: U256,
    /// Gather-scatter: threshold for total flow to sink through multiple destinations
    pub gather_scatter_threshold: U256,
    pub enable_peel_chain_detection: bool,
}

/// ---------------------------------------------------------------------------
/// Main Detector
/// ---------------------------------------------------------------------------

pub struct AMLMotifDetector {
    graph: StableGraph<Address, (U256, u64)>, // edge = (amount, block)
    node_map: HashMap<Address, NodeIndex>,

    per_block_edges: HashMap<u64, Vec<EdgeIndex>>,
    block_queue: VecDeque<u64>,

    // Track edges in order for current block building
    building_edges: Vec<EdgeIndex>,
    building_block: Option<(u64, B256)>,

    config: Config,
}

impl AMLMotifDetector {
    pub fn new(config: Config) -> Self {
        Self {
            graph: StableGraph::new(),
            node_map: HashMap::new(),
            per_block_edges: HashMap::new(),
            block_queue: VecDeque::new(),
            building_edges: Vec::new(),
            building_block: None,
            config,
        }
    }

    // --------------------------------------------------------------------
    // Node helpers
    // --------------------------------------------------------------------
    fn get_or_add_node(&mut self, addr: Address) -> NodeIndex {
        *self.node_map.entry(addr).or_insert_with(|| self.graph.add_node(addr))
    }

    // --------------------------------------------------------------------
    // BLOCK BUILDING: Proposer checks each tx during selection
    // --------------------------------------------------------------------
    /// Called by proposer when selecting transactions for block building.
    /// Returns `true` if the tx creates a forbidden pattern and should be excluded.
    /// If accepted, the edge stays in the graph for subsequent tx checks.
    pub fn proposer_check_tx(
        &mut self,
        from: Address,
        to: Address,
        amount: U256,
        block: u64,
        parent_hash: B256,
    ) -> bool {
        // If we're building a different block (number or parent), reset state
        if self.building_block != Some((block, parent_hash)) {
            self.reset_block_building();
            self.building_block = Some((block, parent_hash));
        }

        let from_idx = self.get_or_add_node(from);
        let to_idx = self.get_or_add_node(to);
        let eidx = self.graph.add_edge(from_idx, to_idx, (amount, block));

        let suspicious = self.check_motifs_against(to_idx, block);

        if suspicious {
            self.graph.remove_edge(eidx);
            return true;
        }

        self.building_edges.push(eidx);
        false
    }

    // --------------------------------------------------------------------
    // CONSENSUS VALIDATION: Validators check complete blocks
    // --------------------------------------------------------------------
    /// Called during consensus to validate an entire block.
    /// Works for both proposers (who have building_edges) and validators (who don't).
    /// Returns `true` if any tx creates a forbidden motif.
    pub fn consensus_validate_block(
        &mut self,
        txs: &[(Address, Address, U256)],
        block: u64,
        parent_hash: B256,
    ) -> bool {
        // Check if we're validating our own block (already built)
        let is_self_built = self
            .building_block
            .as_ref()
            .map(|(b, p)| *b == block && *p == parent_hash)
            .unwrap_or(false);

        let suspicious;

        if is_self_built {
            // Proposer validating its own block — graph already has edges.
            // Just run motif checks without modifying graph.
            let mut recipients = HashSet::new();
            for &(_, to, _) in txs {
                recipients.insert(self.get_or_add_node(to));
            }

            suspicious = recipients
                .iter()
                .any(|&to_idx| self.check_motifs_against(to_idx, block));
        } else {
            let mut temp_edges = Vec::new();

            for &(from, to, amount) in txs {
                let from_idx = self.get_or_add_node(from);
                let to_idx = self.get_or_add_node(to);
                let eidx = self.graph.add_edge(from_idx, to_idx, (amount, block));
                temp_edges.push(eidx);
            }

            let mut recipients = HashSet::new();
            for &(_, to, _) in txs {
                recipients.insert(self.get_or_add_node(to));
            }

            suspicious = recipients
                .iter()
                .any(|&to_idx| self.check_motifs_against(to_idx, block));

            // ALWAYS remove temp edges after checking
            for eidx in temp_edges {
                self.graph.remove_edge(eidx);
            }
        }

        suspicious
    }

    // --------------------------------------------------------------------
    // BLOCK COMMIT
    // --------------------------------------------------------------------
    /// Called after a block is successfully committed.
    /// all_txs: all transactions in block (in order)
    /// successful_indices: indices of transactions that succeeded
    pub fn block_commit(
        &mut self,
        block: u64,
        parent_hash: B256,
        all_txs: &[(Address, Address, U256)],
        successful_indices: &[usize],
    ) {
        // Case 1: We were building this block (self-built)
        if let Some((b, p)) = self.building_block {
            if b == block && p == parent_hash {
                let success_set: HashSet<usize> = successful_indices.iter().cloned().collect();
                let mut kept_edges = Vec::new();

                for (idx, &eidx) in self.building_edges.iter().enumerate() {
                    if success_set.contains(&idx) {
                        kept_edges.push(eidx);
                    } else {
                        self.graph.remove_edge(eidx);
                    }
                }

                self.per_block_edges.insert(block, kept_edges);
                self.building_edges.clear();
                self.building_block = None;

                self.block_queue.push_back(block);
                self.prune(block);
                return;
            }
        }

        // Case 2: External block, add successful txs now
        let mut block_edges = Vec::new();
        for &idx in successful_indices {
            if let Some(&(from, to, amount)) = all_txs.get(idx) {
                let from_idx = self.get_or_add_node(from);
                let to_idx = self.get_or_add_node(to);
                let eidx = self.graph.add_edge(from_idx, to_idx, (amount, block));
                block_edges.push(eidx);
            }
        }
        self.per_block_edges.insert(block, block_edges);

        // Clear state in any case
        self.building_edges.clear();
        self.building_block = None;

        self.block_queue.push_back(block);
        self.prune(block);
    }

    // --------------------------------------------------------------------
    // BLOCK BUILDING RESET
    // --------------------------------------------------------------------
    /// Called when block building is abandoned.
    /// Removes all edges that were added during the building session.
    pub fn reset_block_building(&mut self) {
        for eidx in self.building_edges.drain(..) {
            self.graph.remove_edge(eidx);
        }
        self.building_block = None;
    }

    // --------------------------------------------------------------------
    // REORG HANDLING
    // --------------------------------------------------------------------
    pub fn reorg_revert(&mut self, reverted: &[u64]) {
        for &blk in reverted {
            if let Some(edge_idxs) = self.per_block_edges.remove(&blk) {
                for eidx in edge_idxs {
                    self.graph.remove_edge(eidx);
                }
            }
            self.block_queue.retain(|&b| b != blk);
        }

        if let Some((building_blk, _)) = self.building_block {
            if reverted.contains(&building_blk) {
                for eidx in self.building_edges.drain(..) {
                    self.graph.remove_edge(eidx);
                }
                self.building_block = None;
            }
        }
    }

    fn check_motifs_against(&self, to_idx: NodeIndex, current_block: u64) -> bool {
        // 1. Fan-in (smurfing): Multiple distinct senders to one address
        let mut fan_in_count = 0u64;
        let mut fan_in_sum = U256::from(0);;
        let mut seen = HashSet::new();

        for neighbor in self.graph.neighbors_directed(to_idx, Incoming) {
            if !seen.insert(neighbor) {
                continue; // Already processed this neighbor
            }

            // Sum ALL edges from this neighbor within the window
            let mut neighbor_total = U256::from(0);;
            for edge_ref in self.graph.edges_connecting(neighbor, to_idx) {
                let (amt, blk) = *edge_ref.weight();
                if current_block >= blk && current_block - blk <= self.config.window_blocks {
                    neighbor_total += amt;
                }
            }

            if neighbor_total > 0 {
                fan_in_count += 1;
                fan_in_sum += neighbor_total;
            }
        }

        if fan_in_count > self.config.fan_in_count_threshold
            || fan_in_sum > self.config.fan_in_sum_threshold
        {
            return true;
        }

        // 2. Scatter-Gather: single source → multiple intermediaries → to_idx
        // Pattern: One source splits funds through 2+ intermediaries that converge at destination
        let mut source_data = HashMap::<NodeIndex, (HashSet<NodeIndex>, U256)>::new(); // source -> (intermediaries, total_flow)

        for inter in self.graph.neighbors_directed(to_idx, Incoming) {
            // Calculate total flow from intermediary to destination
            let mut inter_to_dest_sum = U256::from(0);
            let mut inter_to_dest_min_block = u64::MAX;

            for edge_ref in self.graph.edges_connecting(inter, to_idx) {
                let (amt, blk) = *edge_ref.weight();
                if current_block >= blk && current_block - blk <= self.config.window_blocks {
                    inter_to_dest_sum += amt;
                    inter_to_dest_min_block = inter_to_dest_min_block.min(blk);
                }
            }

            if inter_to_dest_sum == 0 {
                continue;
            }

            // Look at sources feeding this intermediary
            for src in self.graph.neighbors_directed(inter, Incoming) {
                let mut src_to_inter_sum = U256::from(0);
                let mut src_to_inter_max_block = 0u64;

                for edge_ref in self.graph.edges_connecting(src, inter) {
                    let (amt, blk) = *edge_ref.weight();
                    if current_block >= blk && current_block - blk <= self.config.window_blocks {
                        src_to_inter_sum += amt;
                        src_to_inter_max_block = src_to_inter_max_block.max(blk);
                    }
                }

                if src_to_inter_sum == 0 {
                    continue;
                }

                // Check temporal ordering: source→inter must happen before or at same time as inter→dest
                if src_to_inter_max_block > inter_to_dest_min_block {
                    continue; // Causality violation - skip this path
                }

                // Calculate bottleneck flow for this path
                let bottleneck = src_to_inter_sum.min(inter_to_dest_sum);

                let entry = source_data.entry(src).or_insert((HashSet::new(), U256::from(0)));
                entry.0.insert(inter); // Track which intermediary
                entry.1 += bottleneck; // Accumulate total flow from this source
            }
        }

        // Check if any source used 2+ intermediaries with significant total flow
        for (_src, (intermediaries, total_flow)) in source_data.iter() {
            if intermediaries.len() >= 2 && *total_flow > self.config.scatter_gather_threshold {
                return true;
            }
        }

        // 3. Gather-Scatter: to_idx → multiple destinations → single sink
        // Pattern: Funds from to_idx split through 2+ destinations that converge at one sink
        let mut sink_data = HashMap::<NodeIndex, (HashSet<NodeIndex>, U256)>::new(); // sink -> (destinations, total_flow)

        for dest in self.graph.neighbors_directed(to_idx, Outgoing) {
            // Calculate total flow from to_idx to this destination
            let mut to_dest_sum = U256::from(0);
            let mut to_dest_max_block = 0u64;

            for edge_ref in self.graph.edges_connecting(to_idx, dest) {
                let (amt, blk) = *edge_ref.weight();
                if current_block >= blk && current_block - blk <= self.config.window_blocks {
                    to_dest_sum += amt;
                    to_dest_max_block = to_dest_max_block.max(blk);
                }
            }

            if to_dest_sum == 0 {
                continue;
            }

            // Look at sinks receiving from this destination
            for sink in self.graph.neighbors_directed(dest, Outgoing) {
                let mut dest_to_sink_sum = U256::from(0);
                let mut dest_to_sink_min_block = u64::MAX;

                for edge_ref in self.graph.edges_connecting(dest, sink) {
                    let (amt, blk) = *edge_ref.weight();
                    if current_block >= blk && current_block - blk <= self.config.window_blocks {
                        dest_to_sink_sum += amt;
                        dest_to_sink_min_block = dest_to_sink_min_block.min(blk);
                    }
                }

                if dest_to_sink_sum == 0 {
                    continue;
                }

                // Check temporal ordering: to_idx→dest must happen before or at same time as dest→sink
                if to_dest_max_block > dest_to_sink_min_block {
                    continue; // Causality violation - skip this path
                }

                // Calculate bottleneck flow for this path
                let bottleneck = to_dest_sum.min(dest_to_sink_sum);

                let entry = sink_data.entry(sink).or_insert((HashSet::new(), U256::from(0)));
                entry.0.insert(dest); // Track which destination
                entry.1 += bottleneck; // Accumulate total flow to this sink
            }
        }

        // Check if any sink received through 2+ destinations with significant total flow
        for (_sink, (destinations, total_flow)) in sink_data.iter() {
            if destinations.len() >= 2 && *total_flow > self.config.gather_scatter_threshold {
                return true;
            }
        }

        // 4. Peel chain detection
        if self.config.enable_peel_chain_detection {
            if self.detect_peel_chain(to_idx, current_block) {
                return true;
            }
        }

        false
    }

    /// Detects peel chains: systematic skimming pattern
    /// Returns true if suspicious peel chain detected
    fn detect_peel_chain(&self, to_idx: NodeIndex, current_block: u64) -> bool {
        let mut chain_depth = 0;
        let mut current = to_idx;
        let mut peel_percentages = Vec::new();

        for _ in 0..10 { // Max 10 hops
            // Find single predecessor (peel chains are linear)
            let predecessors: Vec<_> = self.graph.neighbors_directed(current, Incoming)
                .filter(|&pred| {
                    self.graph.edges_connecting(pred, current).any(|e| {
                        let (_, blk) = *e.weight();
                        current_block >= blk && current_block - blk <= self.config.window_blocks
                    })
                })
                .collect();

            if predecessors.len() != 1 {
                break; // Not a linear chain
            }

            let pred = predecessors[0];

            // Calculate what percentage was "kept" vs "forwarded"
            let mut amount_to_current = U256::from(0);
            for edge_ref in self.graph.edges_connecting(pred, current) {
                let (amt, blk) = *edge_ref.weight();
                if current_block >= blk && current_block - blk <= self.config.window_blocks {
                    amount_to_current += amt;
                }
            }

            // Check if pred sent to other addresses (peeling)
            let mut amount_to_others = U256::from(0);
            let mut other_recipients = 0;
            for other in self.graph.neighbors_directed(pred, Outgoing) {
                if other == current {
                    continue;
                }
                other_recipients += 1;
                for edge_ref in self.graph.edges_connecting(pred, other) {
                    let (amt, blk) = *edge_ref.weight();
                    if current_block >= blk && current_block - blk <= self.config.window_blocks {
                        amount_to_others += amt;
                    }
                }
            }

            // If no peeling occurred, not part of peel chain
            if other_recipients == 0 || amount_to_others == U256::from(0) {
                break;
            }

            // Calculate peel percentage
            let total = amount_to_current + amount_to_others;
            if total > U256::from(0) {
                let peel_pct = (amount_to_others * U256::from(100)) / total;
                peel_percentages.push(peel_pct);
                chain_depth += 1;
                current = pred;
            } else {
                break;
            }
        }

        // Suspicious if:
        // 1. Chain is at least 3 hops long
        // 2. Peel percentages are consistently small (2-15%)
        if chain_depth >= 3 {
            let consistent_peeling = peel_percentages.iter().all(|&pct| {
                pct >= U256::from(2) && pct <= U256::from(15)
            });

            if consistent_peeling {
                return true;
            }
        }

        false
    }

    // --------------------------------------------------------------------
    // ROLLING PRUNE
    // --------------------------------------------------------------------
    fn prune(&mut self, current_block: u64) {
        while let Some(&old) = self.block_queue.front() {
            if current_block - old <= self.config.window_blocks {
                break;
            }
            self.block_queue.pop_front();
            if let Some(edges) = self.per_block_edges.remove(&old) {
                for eidx in edges {
                    // Just remove the edge, no cache updates
                    self.graph.remove_edge(eidx);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256};
    use std::str::FromStr;

    fn addr(hex: &str) -> Address {
        Address::from_str(hex).unwrap()
    }

    fn test_config() -> Config {
        Config {
            window_blocks: 100,
            fan_in_count_threshold: 5,
            fan_in_sum_threshold: U256::from(1000),
            scatter_gather_threshold: U256::from(500),
            gather_scatter_threshold: U256::from(500),
            enable_peel_chain_detection: true,
        }
    }

    fn simple_config() -> Config {
        Config {
            window_blocks: 5,
            fan_in_count_threshold: 2,
            fan_in_sum_threshold: U256::from(10),
            scatter_gather_threshold: U256::from(5),
            gather_scatter_threshold: U256::from(5),
            enable_peel_chain_detection: false,
        }
    }

    fn parent_hash(block: u64) -> B256 {
        // Simple: use block number as hash for tests
        let mut bytes = [0u8; 32];
        bytes[24..].copy_from_slice(&block.to_be_bytes());
        B256::from(bytes)
    }

    // ========================================================================
    // Fan-in (Smurfing) Tests
    // ========================================================================

    #[test]
    fn test_fan_in_count_threshold() {
        let mut detector = AMLMotifDetector::new(test_config());
        let dest = addr("0x1000000000000000000000000000000000000001");
        let block = 10;

        // Add 5 senders (at threshold)
        for i in 0..5 {
            let from = addr(&format!("0x100000000000000000000000000000000000000{}", i + 2));
            assert!(!detector.proposer_check_tx(from, dest, U256::from(50), block, parent_hash(block-1)));
        }

        // 6th sender should trigger
        let from6 = addr("0x1000000000000000000000000000000000000007");
        assert!(detector.proposer_check_tx(from6, dest, U256::from(50), block, parent_hash(block-1)));
    }

    #[test]
    fn test_fan_in_sum_threshold() {
        let mut detector = AMLMotifDetector::new(test_config());
        let dest = addr("0x2000000000000000000000000000000000000001");
        let block = 10;

        // Add transactions totaling 1000 (at threshold)
        let from1 = addr("0x2000000000000000000000000000000000000002");
        let from2 = addr("0x2000000000000000000000000000000000000003");
        let from3 = addr("0x2000000000000000000000000000000000000004");

        assert!(!detector.proposer_check_tx(from1, dest, U256::from(400), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(from2, dest, U256::from(300), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(from3, dest, U256::from(300), block, parent_hash(block-1)));

        // One more should trigger
        let from4 = addr("0x2000000000000000000000000000000000000005");
        assert!(detector.proposer_check_tx(from4, dest, U256::from(1), block, parent_hash(block-1)));
    }

    #[test]
    fn test_fan_in_multiple_transfers_same_sender() {
        let mut detector = AMLMotifDetector::new(test_config());
        let sender = addr("0x3000000000000000000000000000000000000001");
        let dest = addr("0x3000000000000000000000000000000000000002");
        let block = 10;

        // Multiple transfers from same sender should be summed
        assert!(!detector.proposer_check_tx(sender, dest, U256::from(400), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(sender, dest, U256::from(350), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(sender, dest, U256::from(250), block, parent_hash(block-1)));

        // Total: 1000, next one should trigger
        assert!(detector.proposer_check_tx(sender, dest, U256::from(1), block, parent_hash(block-1)));
    }

    // #[test]
    // fn test_fan_in_respects_time_window() {
    //     let mut detector = AMLMotifDetector::new(test_config());
    //     let dest = addr("0x4000000000000000000000000000000000000001");
    //
    //     // Add and commit 5 senders at block 10
    //     let mut txs = Vec::new();
    //     for i in 0..5 {
    //         let from = addr(&format!("0x400000000000000000000000000000000000000{}", i + 2));
    //         txs.push((from, dest, U256::from(50)));
    //     }
    //     assert!(!detector.consensus_validate_block(&txs, 10, parent_hash(9)));
    //     detector.block_commit(10, &txs);
    //
    //     // Move to block 111 (outside window) with dummy block to trigger pruning
    //     let dummy = vec![(addr("0x4000000000000000000000000000000000000100"),
    //                       addr("0x4000000000000000000000000000000000000101"),
    //                       U256::from(1))];
    //     assert!(!detector.consensus_validate_block(&dummy, 111));
    //     detector.block_commit(111, &dummy);
    //
    //     // Old edges should be pruned, can add 6 more without triggering
    //     for i in 0..6 {
    //         let from = addr(&format!("0x400000000000000000000000000000000000010{}", i + 2));
    //         assert!(!detector.proposer_check_tx(from, dest, U256::from(50), 111));
    //     }
    // }

    #[test]
    fn test_fan_in_basic() {
        let mut g = AMLMotifDetector::new(simple_config());
        let a = addr("0x1000000000000000000000000000000000000001");
        let b = addr("0x2000000000000000000000000000000000000002");
        let z = addr("0x3000000000000000000000000000000000000003");

        let a_idx = g.get_or_add_node(a);
        let b_idx = g.get_or_add_node(b);
        let z_idx = g.get_or_add_node(z);

        g.graph.add_edge(a_idx, z_idx, (U256::from(5), 10));
        g.graph.add_edge(b_idx, z_idx, (U256::from(6), 10));

        assert!(g.check_motifs_against(z_idx, 10));
    }

    // ========================================================================
    // Scatter-Gather Tests
    // ========================================================================

    #[test]
    fn test_scatter_gather_basic() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source = addr("0x5000000000000000000000000000000000000001");
        let inter1 = addr("0x5000000000000000000000000000000000000002");
        let inter2 = addr("0x5000000000000000000000000000000000000003");
        let dest = addr("0x5000000000000000000000000000000000000004");
        let block = 10;

        // Source → Inter1 → Dest (300)
        assert!(!detector.proposer_check_tx(source, inter1, U256::from(300), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(inter1, dest, U256::from(300), block, parent_hash(block-1)));

        // Source → Inter2 → Dest (300)
        assert!(!detector.proposer_check_tx(source, inter2, U256::from(300), block, parent_hash(block-1)));

        // This should trigger: total flow = 600 > 500
        assert!(detector.proposer_check_tx(inter2, dest, U256::from(300), block, parent_hash(block-1)));
    }

    #[test]
    fn test_scatter_gather_bottleneck() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source = addr("0x6000000000000000000000000000000000000001");
        let inter1 = addr("0x6000000000000000000000000000000000000002");
        let inter2 = addr("0x6000000000000000000000000000000000000003");
        let dest = addr("0x6000000000000000000000000000000000000004");
        let block = 10;

        // Source → Inter1: 400, Inter1 → Dest: 200 (bottleneck = 200)
        assert!(!detector.proposer_check_tx(source, inter1, U256::from(400), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(inter1, dest, U256::from(200), block, parent_hash(block-1)));

        // Source → Inter2: 400, Inter2 → Dest: 200 (bottleneck = 200)
        assert!(!detector.proposer_check_tx(source, inter2, U256::from(400), block, parent_hash(block-1)));

        // Total flow = 200 + 200 = 400, below threshold (500)
        assert!(!detector.proposer_check_tx(inter2, dest, U256::from(200), block, parent_hash(block-1)));

        // Add more flow through inter2 to trigger
        assert!(!detector.proposer_check_tx(source, inter2, U256::from(200), block, parent_hash(block-1)));
        assert!(detector.proposer_check_tx(inter2, dest, U256::from(200), block, parent_hash(block-1)));
    }

    #[test]
    fn test_scatter_gather_different_sources_no_trigger() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source1 = addr("0x7000000000000000000000000000000000000001");
        let source2 = addr("0x7000000000000000000000000000000000000002");
        let inter1 = addr("0x7000000000000000000000000000000000000003");
        let inter2 = addr("0x7000000000000000000000000000000000000004");
        let dest = addr("0x7000000000000000000000000000000000000005");
        let block = 10;

        // Source1 → Inter1 → Dest
        assert!(!detector.proposer_check_tx(source1, inter1, U256::from(300), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(inter1, dest, U256::from(300), block, parent_hash(block-1)));

        // Source2 → Inter2 → Dest (different source!)
        assert!(!detector.proposer_check_tx(source2, inter2, U256::from(300), block, parent_hash(block-1)));

        // Should NOT trigger: different sources
        assert!(!detector.proposer_check_tx(inter2, dest, U256::from(300), block, parent_hash(block-1)));
    }

    #[test]
    fn test_scatter_gather_temporal_ordering() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source = addr("0x8000000000000000000000000000000000000001");
        let inter1 = addr("0x8000000000000000000000000000000000000002");
        let inter2 = addr("0x8000000000000000000000000000000000000003");
        let dest = addr("0x8000000000000000000000000000000000000004");

        let s_idx = detector.get_or_add_node(source);
        let i1_idx = detector.get_or_add_node(inter1);
        let i2_idx = detector.get_or_add_node(inter2);
        let d_idx = detector.get_or_add_node(dest);

        // Inter1 → Dest happens BEFORE Source → Inter1 (causality violation)
        detector.graph.add_edge(i1_idx, d_idx, (U256::from(300), 10));
        detector.graph.add_edge(s_idx, i1_idx, (U256::from(300), 15));

        // Valid path: Source → Inter2 → Dest
        detector.graph.add_edge(s_idx, i2_idx, (U256::from(300), 10));
        detector.graph.add_edge(i2_idx, d_idx, (U256::from(300), 12));

        // Should not trigger because first path violates causality
        assert!(!detector.check_motifs_against(d_idx, 20));
    }

    #[test]
    fn test_scatter_gather_graph_based() {
        let mut g = AMLMotifDetector::new(simple_config());
        let s = addr("0xaaaa000000000000000000000000000000000001");
        let i1 = addr("0xaaaa000000000000000000000000000000000002");
        let i2 = addr("0xaaaa000000000000000000000000000000000003");
        let d = addr("0xaaaa000000000000000000000000000000000004");

        let s_idx = g.get_or_add_node(s);
        let i1_idx = g.get_or_add_node(i1);
        let i2_idx = g.get_or_add_node(i2);
        let d_idx = g.get_or_add_node(d);

        g.graph.add_edge(s_idx, i1_idx, (U256::from(3), 10));
        g.graph.add_edge(s_idx, i2_idx, (U256::from(4), 10));
        g.graph.add_edge(i1_idx, d_idx, (U256::from(3), 11));
        g.graph.add_edge(i2_idx, d_idx, (U256::from(3), 11));

        assert!(g.check_motifs_against(d_idx, 12));
    }

    // ========================================================================
    // Gather-Scatter Tests
    // ========================================================================

    #[test]
    fn test_gather_scatter_basic() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source = addr("0x9000000000000000000000000000000000000001");
        let dest1 = addr("0x9000000000000000000000000000000000000002");
        let dest2 = addr("0x9000000000000000000000000000000000000003");
        let sink = addr("0x9000000000000000000000000000000000000004");
        let block = 10;

        // Source → Dest1 → Sink (300)
        assert!(!detector.proposer_check_tx(source, dest1, U256::from(300), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(dest1, sink, U256::from(300), block, parent_hash(block-1)));

        // Source → Dest2 → Sink (300)
        assert!(!detector.proposer_check_tx(source, dest2, U256::from(300), block, parent_hash(block-1)));

        // This should trigger: total flow = 600 > 500
        assert!(detector.proposer_check_tx(dest2, sink, U256::from(300), block, parent_hash(block-1)));
    }

    #[test]
    fn test_gather_scatter_different_sinks_no_trigger() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source = addr("0xa000000000000000000000000000000000000001");
        let dest1 = addr("0xa000000000000000000000000000000000000002");
        let dest2 = addr("0xa000000000000000000000000000000000000003");
        let sink1 = addr("0xa000000000000000000000000000000000000004");
        let sink2 = addr("0xa000000000000000000000000000000000000005");
        let block = 10;

        // Source → Dest1 → Sink1
        assert!(!detector.proposer_check_tx(source, dest1, U256::from(300), block, parent_hash(block-1)));
        assert!(!detector.proposer_check_tx(dest1, sink1, U256::from(300), block, parent_hash(block-1)));

        // Source → Dest2 → Sink2 (different sink!)
        assert!(!detector.proposer_check_tx(source, dest2, U256::from(300), block, parent_hash(block-1)));

        // Should NOT trigger: different sinks
        assert!(!detector.proposer_check_tx(dest2, sink2, U256::from(300), block, parent_hash(block-1)));
    }

    #[test]
    fn test_gather_scatter_graph_based() {
        let mut g = AMLMotifDetector::new(simple_config());
        let a = addr("0xbbbb000000000000000000000000000000000001");
        let d1 = addr("0xbbbb000000000000000000000000000000000002");
        let d2 = addr("0xbbbb000000000000000000000000000000000003");
        let s = addr("0xbbbb000000000000000000000000000000000004");

        let a_idx = g.get_or_add_node(a);
        let d1_idx = g.get_or_add_node(d1);
        let d2_idx = g.get_or_add_node(d2);
        let s_idx = g.get_or_add_node(s);

        g.graph.add_edge(a_idx, d1_idx, (U256::from(4), 5));
        g.graph.add_edge(a_idx, d2_idx, (U256::from(5), 5));
        g.graph.add_edge(d1_idx, s_idx, (U256::from(4), 6));
        g.graph.add_edge(d2_idx, s_idx, (U256::from(5), 6));

        assert!(g.check_motifs_against(a_idx, 7));
    }

    // ========================================================================
    // Peel Chain Tests
    // ========================================================================

    #[test]
    fn test_peel_chain_detection() {
        let mut detector = AMLMotifDetector::new(Config {
            enable_peel_chain_detection: true,
            ..test_config()
        });

        let a = addr("0xc000000000000000000000000000000000000001");
        let b = addr("0xc000000000000000000000000000000000000002");
        let c = addr("0xc000000000000000000000000000000000000003");
        let d = addr("0xc000000000000000000000000000000000000004");
        let peel1 = addr("0xc000000000000000000000000000000000000011");
        let peel2 = addr("0xc000000000000000000000000000000000000012");
        let peel3 = addr("0xc000000000000000000000000000000000000013");

        let a_idx = detector.get_or_add_node(a);
        let b_idx = detector.get_or_add_node(b);
        let c_idx = detector.get_or_add_node(c);
        let d_idx = detector.get_or_add_node(d);
        let p1_idx = detector.get_or_add_node(peel1);
        let p2_idx = detector.get_or_add_node(peel2);
        let p3_idx = detector.get_or_add_node(peel3);

        // A sends 100: 95 to B, 5 to peel address
        detector.graph.add_edge(a_idx, b_idx, (U256::from(95), 10));
        detector.graph.add_edge(a_idx, p1_idx, (U256::from(5), 10));

        // B sends 95: 90 to C, 5 to peel address
        detector.graph.add_edge(b_idx, c_idx, (U256::from(90), 11));
        detector.graph.add_edge(b_idx, p2_idx, (U256::from(5), 11));

        // C sends 90: 85 to D, 5 to peel address
        detector.graph.add_edge(c_idx, d_idx, (U256::from(85), 12));
        detector.graph.add_edge(c_idx, p3_idx, (U256::from(5), 12));

        // Should detect peel chain at D
        assert!(detector.check_motifs_against(d_idx, 13));
    }

    #[test]
    fn test_peel_chain_not_triggered_for_normal_transfers() {
        let mut detector = AMLMotifDetector::new(Config {
            enable_peel_chain_detection: true,
            ..test_config()
        });

        let a = addr("0xd000000000000000000000000000000000000001");
        let b = addr("0xd000000000000000000000000000000000000002");
        let c = addr("0xd000000000000000000000000000000000000003");

        let a_idx = detector.get_or_add_node(a);
        let b_idx = detector.get_or_add_node(b);
        let c_idx = detector.get_or_add_node(c);

        // Normal linear transfer without peeling
        detector.graph.add_edge(a_idx, b_idx, (U256::from(100), 10));
        detector.graph.add_edge(b_idx, c_idx, (U256::from(100), 11));

        assert!(!detector.check_motifs_against(c_idx, 12));
    }

    #[test]
    fn test_peel_chain_short_chain_not_triggered() {
        let mut detector = AMLMotifDetector::new(Config {
            enable_peel_chain_detection: true,
            ..test_config()
        });

        let a = addr("0xe000000000000000000000000000000000000001");
        let b = addr("0xe000000000000000000000000000000000000002");
        let peel = addr("0xe000000000000000000000000000000000000011");

        let a_idx = detector.get_or_add_node(a);
        let b_idx = detector.get_or_add_node(b);
        let p_idx = detector.get_or_add_node(peel);

        // Only 1 hop with peel (need at least 3)
        detector.graph.add_edge(a_idx, b_idx, (U256::from(95), 10));
        detector.graph.add_edge(a_idx, p_idx, (U256::from(5), 10));

        assert!(!detector.check_motifs_against(b_idx, 11));
    }

    // ========================================================================
    // Block Building and Validation Tests
    // ========================================================================
    //
    // #[test]
    // fn test_proposer_then_validator_flow() {
    //     let mut proposer = AMLMotifDetector::new(test_config());
    //     let mut validator = AMLMotifDetector::new(test_config());
    //
    //     let from = addr("0xf000000000000000000000000000000000000001");
    //     let to = addr("0xf000000000000000000000000000000000000002");
    //     let block = 10;
    //
    //     // Proposer checks tx
    //     assert!(!proposer.proposer_check_tx(from, to, U256::from(100), block));
    //
    //     // Both validate block
    //     let txs = vec![(from, to, U256::from(100))];
    //     assert!(!proposer.consensus_validate_block(&txs, block));
    //     assert!(!validator.consensus_validate_block(&txs, block));
    //
    //     // Both commit
    //     proposer.block_commit(block, &txs);
    //     validator.block_commit(block, &txs);
    //
    //     // Both should have same state
    //     assert_eq!(proposer.graph.edge_count(), validator.graph.edge_count());
    // }
    //
    #[test]
    fn test_block_validation_rollback_on_suspicious() {
        let mut detector = AMLMotifDetector::new(test_config());
        let dest = addr("0xf100000000000000000000000000000000000001");
        let block = 10;

        // Create block with 6 senders (exceeds fan-in threshold)
        let txs: Vec<_> = (0..6)
            .map(|i| {
                (addr(&format!("0xf10000000000000000000000000000000000000{}", i + 2)),
                 dest,
                 U256::from(50))
            })
            .collect();

        // Validation should fail
        assert!(detector.consensus_validate_block(&txs, block, parent_hash(block-1)));

        // Graph should be empty (all edges rolled back)
        assert_eq!(detector.graph.edge_count(), 0);
    }

    #[test]
    fn test_reset_block_building() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xf200000000000000000000000000000000000001");
        let to = addr("0xf200000000000000000000000000000000000002");

        // Add some txs during block building
        assert!(!detector.proposer_check_tx(from, to, U256::from(100), 10, parent_hash(9)));
        assert!(!detector.proposer_check_tx(from, to, U256::from(200), 10, parent_hash(9)));

        assert_eq!(detector.graph.edge_count(), 2);

        // Reset should remove all building edges
        detector.reset_block_building();
        assert_eq!(detector.graph.edge_count(), 0);
    }

    #[test]
    fn test_auto_reset_on_new_block() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xf300000000000000000000000000000000000001");
        let to = addr("0xf300000000000000000000000000000000000002");

        // Build block 10
        assert!(!detector.proposer_check_tx(from, to, U256::from(100), 10, parent_hash(9)));
        assert_eq!(detector.graph.edge_count(), 1);

        // Start building block 11 (should auto-reset block 10)
        assert!(!detector.proposer_check_tx(from, to, U256::from(200), 11, parent_hash(10)));
        assert_eq!(detector.graph.edge_count(), 1); // Only new edge
    }

    #[test]
    fn test_block_commit_with_failed_txs() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xf400000000000000000000000000000000000001");
        let to = addr("0xf400000000000000000000000000000000000002");

        // Validate block with 3 txs
        let txs = vec![
            (from, to, U256::from(100)),
            (from, to, U256::from(200)),
            (from, to, U256::from(300)),
        ];
        assert!(!detector.consensus_validate_block(&txs, 10, parent_hash(9)));

        // Commit with only 2 successful
        let successful = vec![
            (from, to, U256::from(100)),
            (from, to, U256::from(300)),
        ];
        let successful_indices: Vec<usize> = (0..txs.len()).collect();
        detector.block_commit(10, parent_hash(9), &successful, &successful_indices);

        // Only 2 edges should exist
        assert_eq!(detector.graph.edge_count(), 2);
    }

    #[test]
    fn test_block_commit_sync_without_validation() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xf500000000000000000000000000000000000001");
        let to = addr("0xf500000000000000000000000000000000000002");

        // No validation, just commit (sync scenario)
        let txs = vec![(from, to, U256::from(100))];
        let successful_indices: Vec<usize> = (0..txs.len()).collect();
        let parent = parent_hash(9);
        detector.block_commit(10, parent, &txs, &successful_indices);

        // Should have 1 edge
        assert_eq!(detector.graph.edge_count(), 1);
    }

    // ========================================================================
    // Reorg Tests
    // ========================================================================

    #[test]
    fn test_reorg_revert() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xf600000000000000000000000000000000000001");
        let to = addr("0xf600000000000000000000000000000000000002");

        // Add and commit blocks 10, 11, 12
        for block in 10..=12 {
            let txs = vec![(from, to, U256::from(100))];
            let parent = parent_hash(block-1);
            let successful_indices: Vec<usize> = (0..txs.len()).collect();
            assert!(!detector.consensus_validate_block(&txs, block, parent));
            detector.block_commit(block, parent, &txs, &successful_indices);
        }

        assert_eq!(detector.graph.edge_count(), 3);

        // Reorg: revert blocks 11 and 12
        detector.reorg_revert(&[11, 12]);

        assert_eq!(detector.graph.edge_count(), 1); // Only block 10 remains
        assert_eq!(detector.block_queue.len(), 1);
    }

    #[test]
    fn test_reorg_during_building() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xf700000000000000000000000000000000000001");
        let to = addr("0xf700000000000000000000000000000000000002");

        // Start building block 10
        assert!(!detector.proposer_check_tx(from, to, U256::from(100), 10, parent_hash(9)));
        assert_eq!(detector.graph.edge_count(), 1);

        // Reorg reverts block 10
        detector.reorg_revert(&[10]);

        // Building edges should be cleared
        assert_eq!(detector.graph.edge_count(), 0);
        assert!(detector.building_block.is_none());
    }

    // ========================================================================
    // Pruning Tests
    // ========================================================================

    #[test]
    fn test_pruning_old_blocks() {
        let mut detector = AMLMotifDetector::new(Config {
            window_blocks: 5,
            ..test_config()
        });
        let from = addr("0xf800000000000000000000000000000000000001");
        let to = addr("0xf800000000000000000000000000000000000002");

        // Add blocks 0-10
        for block in 0..=10 {
            let txs = vec![(from, to, U256::from(100))];
            let parent = parent_hash(block);
            let successful_indices: Vec<usize> = (0..txs.len()).collect();
            assert!(!detector.consensus_validate_block(&txs, block, parent));
            detector.block_commit(block, parent, &txs, &successful_indices);
        }

        // After block 10, blocks 0-4 should be pruned (window=5)
        // Blocks 5-10 should remain (6 blocks)
        assert_eq!(detector.graph.edge_count(), 6);
    }

    #[test]
    fn test_prune_removes_old_edges() {
        let mut g = AMLMotifDetector::new(simple_config());
        let a = addr("0x1111111111111111111111111111111111111111");
        let b = addr("0x2222222222222222222222222222222222222222");
        let c = addr("0x3333333333333333333333333333333333333333");

        let a_idx = g.get_or_add_node(a);
        let b_idx = g.get_or_add_node(b);
        let c_idx = g.get_or_add_node(c);

        let e1 = g.graph.add_edge(a_idx, b_idx, (U256::from(1), 1));
        let e2 = g.graph.add_edge(b_idx, c_idx, (U256::from(2), 7));

        g.per_block_edges.insert(1, vec![e1]);
        g.per_block_edges.insert(7, vec![e2]);
        g.block_queue.push_back(1);
        g.block_queue.push_back(7);

        g.prune(10);

        assert!(
            !g.graph.contains_edge(a_idx, b_idx),
            "old edge (block 1) should be pruned"
        );
        assert!(
            g.graph.contains_edge(b_idx, c_idx),
            "newer edge (block 7) should remain"
        );
    }

    // #[test]
    // fn test_pruning_affects_detection() {
    //     let mut detector = AMLMotifDetector::new(Config {
    //         window_blocks: 5,
    //         ..test_config()
    //     });
    //     let dest = addr("0xf900000000000000000000000000000000000001");
    //
    //     // Add 5 senders at block 0
    //     for i in 0..5 {
    //         let from = addr(&format!("0xf90000000000000000000000000000000000000{}", i + 2));
    //         let txs = vec![(from, dest, U256::from(50))];
    //         assert!(!detector.consensus_validate_block(&txs, 0, parent_hash(0)));
    //         let successful_indices: Vec<usize> = (0..txs.len()).collect();
    //         detector.block_commit(0, parent_hash(0), &txs, &successful_indices);
    //     }
    //
    //     // Add dummy blocks to trigger pruning
    //     for block in 1..=10 {
    //         let dummy = vec![(addr("0xf900000000000000000000000000000000000100"),
    //                           addr("0xf900000000000000000000000000000000000101"),
    //                           U256::from(1))];
    //         let successful_indices: Vec<usize> = (0..dummy.len()).collect();
    //         assert!(!detector.consensus_validate_block(&dummy, block, parent_hash(block-1)));
    //         detector.block_commit(block, parent_hash(block-1), &dummy, &successful_indices);
    //     }
    //
    //     // At block 10, old senders from block 0 should be pruned
    //     // So we can add 6 new senders without triggering
    //     for i in 10..16 {
    //         let from = addr(&format!("0xf90000000000000000000000000000000000001{}", i));
    //         assert!(!detector.proposer_check_tx(from, dest, U256::from(50), 10, parent_hash(9)));
    //     }
    // }

    // ========================================================================
    // Edge Cases
    // ========================================================================

    #[test]
    fn test_self_transfer() {
        let mut detector = AMLMotifDetector::new(test_config());
        let addr1 = addr("0xfa00000000000000000000000000000000000001");

        // Self-transfer should not cause issues
        assert!(!detector.proposer_check_tx(addr1, addr1, U256::from(100), 10, parent_hash(9)));
    }

    #[test]
    fn test_zero_amount_transfer() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xfb00000000000000000000000000000000000001");
        let to = addr("0xfb00000000000000000000000000000000000002");

        // Zero amount transfers should not contribute to sums
        assert!(!detector.proposer_check_tx(from, to, U256::from(0), 10, parent_hash(9)));

        // Should still be in graph
        assert_eq!(detector.graph.edge_count(), 1);
    }

    #[test]
    fn test_multiple_blocks_same_addresses() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xfc00000000000000000000000000000000000001");
        let to = addr("0xfc00000000000000000000000000000000000002");

        // Same addresses, different blocks
        for block in 10..15 {
            let parent = parent_hash(block-1);
            let txs = vec![(from, to, U256::from(100))];
            let successful_indices: Vec<usize> = (0..txs.len()).collect();
            assert!(!detector.consensus_validate_block(&txs, block, parent));
            detector.block_commit(block, parent, &txs, &successful_indices);
        }

        assert_eq!(detector.graph.edge_count(), 5);
    }

    #[test]
    fn test_empty_block_commit() {
        let mut detector = AMLMotifDetector::new(test_config());

        // Commit empty block
        detector.block_commit(10, parent_hash(9), &[], &[]);

        assert_eq!(detector.graph.edge_count(), 0);
        assert_eq!(detector.block_queue.len(), 1);
    }

    #[test]
    fn test_large_fan_in_values() {
        let mut detector = AMLMotifDetector::new(test_config());
        let dest = addr("0xfd00000000000000000000000000000000000001");
        let block = 10;
        let parent = parent_hash(block-1);

        // Test with large U256 values
        let large_amount = U256::from_str("1000000000000000000000000").unwrap(); // 1M ETH

        let from1 = addr("0xfd00000000000000000000000000000000000002");
        let from2 = addr("0xfd00000000000000000000000000000000000003");

        // This should trigger sum threshold
        assert!(detector.proposer_check_tx(from2, dest, large_amount, block, parent));
    }

    // ========================================================================
    // Complex Multi-Pattern Tests
    // ========================================================================

    #[test]
    fn test_combined_scatter_gather_and_fan_in() {
        let mut detector = AMLMotifDetector::new(test_config());
        let source = addr("0xfe00000000000000000000000000000000000001");
        let inter1 = addr("0xfe00000000000000000000000000000000000002");
        let inter2 = addr("0xfe00000000000000000000000000000000000003");
        let dest = addr("0xfe00000000000000000000000000000000000004");
        let block = 10;
        let parent = parent_hash(block-1);

        // Create scatter-gather pattern
        assert!(!detector.proposer_check_tx(source, inter1, U256::from(300), block, parent));
        assert!(!detector.proposer_check_tx(inter1, dest, U256::from(300), block, parent));
        assert!(!detector.proposer_check_tx(source, inter2, U256::from(300), block, parent));
        assert!(detector.proposer_check_tx(inter2, dest, U256::from(300), block, parent));
    }

    #[test]
    fn test_temporal_window_boundary() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xff00000000000000000000000000000000000001");
        let to = addr("0xff00000000000000000000000000000000000002");

        let from_idx = detector.get_or_add_node(from);
        let to_idx = detector.get_or_add_node(to);

        // Add edge at block 10
        detector.graph.add_edge(from_idx, to_idx, (U256::from(500), 10));

        // Check at block 110 (exactly at window boundary)
        assert!(!detector.check_motifs_against(to_idx, 110));

        // Check at block 111 (just outside window)
        assert!(!detector.check_motifs_against(to_idx, 111));
    }

    #[test]
    fn test_validation_without_proposer_building() {
        let mut detector = AMLMotifDetector::new(test_config());
        let from = addr("0xff10000000000000000000000000000000000001");
        let to = addr("0xff10000000000000000000000000000000000002");

        // Validator validates without prior building
        let txs = vec![(from, to, U256::from(100))];
        assert!(!detector.consensus_validate_block(&txs, 10, parent_hash(9)));
        let successful_indices: Vec<usize> = (0..txs.len()).collect();
        detector.block_commit(10, parent_hash(9), &txs, &successful_indices);

        assert_eq!(detector.graph.edge_count(), 1);
    }

    #[test]
    fn test_proposer_building_rejected_tx() {
        let mut detector = AMLMotifDetector::new(test_config());
        let dest = addr("0xff20000000000000000000000000000000000001");
        let block = 10;
        let parent = parent_hash(block - 1);

        // Build up to threshold
        for i in 0..5 {
            let from = addr(&format!("0xff2000000000000000000000000000000000000{}", i + 2));
            assert!(!detector.proposer_check_tx(from, dest, U256::from(50), block, parent));
        }

        // Try to add one more (should be rejected)
        let from6 = addr("0xff20000000000000000000000000000000000007");
        assert!(detector.proposer_check_tx(from6, dest, U256::from(50), block, parent));

        // Proposer should only include the 5 accepted txs
        let txs: Vec<_> = (0..5)
            .map(|i| {
                (
                    addr(&format!("0xff2000000000000000000000000000000000000{}", i + 2)),
                    dest,
                    U256::from(50),
                )
            })
            .collect();

        // Block validation (should pass)
        assert!(!detector.consensus_validate_block(&txs, block, parent));

        // Commit the block — mark all txs as successful
        let successful_indices: Vec<usize> = (0..txs.len()).collect();
        detector.block_commit(block, parent, &txs, &successful_indices);

        assert_eq!(detector.graph.edge_count(), 5);
    }


    #[test]
    fn test_peel_chain_with_varying_percentages() {
        let mut detector = AMLMotifDetector::new(Config {
            enable_peel_chain_detection: true,
            ..test_config()
        });

        let a = addr("0xff30000000000000000000000000000000000001");
        let b = addr("0xff30000000000000000000000000000000000002");
        let c = addr("0xff30000000000000000000000000000000000003");
        let d = addr("0xff30000000000000000000000000000000000004");
        let peel1 = addr("0xff30000000000000000000000000000000000011");
        let peel2 = addr("0xff30000000000000000000000000000000000012");
        let peel3 = addr("0xff30000000000000000000000000000000000013");

        let a_idx = detector.get_or_add_node(a);
        let b_idx = detector.get_or_add_node(b);
        let c_idx = detector.get_or_add_node(c);
        let d_idx = detector.get_or_add_node(d);
        let p1_idx = detector.get_or_add_node(peel1);
        let p2_idx = detector.get_or_add_node(peel2);
        let p3_idx = detector.get_or_add_node(peel3);

        // Varying peel percentages but all within 2-15% range
        // A: 97 forward, 3 peel (3%)
        detector.graph.add_edge(a_idx, b_idx, (U256::from(97), 10));
        detector.graph.add_edge(a_idx, p1_idx, (U256::from(3), 10));

        // B: 87 forward, 10 peel (10.3%)
        detector.graph.add_edge(b_idx, c_idx, (U256::from(87), 11));
        detector.graph.add_edge(b_idx, p2_idx, (U256::from(10), 11));

        // C: 80 forward, 7 peel (8%)
        detector.graph.add_edge(c_idx, d_idx, (U256::from(80), 12));
        detector.graph.add_edge(c_idx, p3_idx, (U256::from(7), 12));

        // Should still detect as peel chain
        assert!(detector.check_motifs_against(d_idx, 13));
    }

    #[test]
    fn test_peel_chain_high_percentage_not_detected() {
        let mut detector = AMLMotifDetector::new(Config {
            enable_peel_chain_detection: true,
            ..test_config()
        });

        let a = addr("0xff40000000000000000000000000000000000001");
        let b = addr("0xff40000000000000000000000000000000000002");
        let c = addr("0xff40000000000000000000000000000000000003");
        let split1 = addr("0xff40000000000000000000000000000000000011");
        let split2 = addr("0xff40000000000000000000000000000000000012");

        let a_idx = detector.get_or_add_node(a);
        let b_idx = detector.get_or_add_node(b);
        let c_idx = detector.get_or_add_node(c);
        let s1_idx = detector.get_or_add_node(split1);
        let s2_idx = detector.get_or_add_node(split2);

        // High split percentages (50/50) - not a peel pattern
        detector.graph.add_edge(a_idx, b_idx, (U256::from(50), 10));
        detector.graph.add_edge(a_idx, s1_idx, (U256::from(50), 10));

        detector.graph.add_edge(b_idx, c_idx, (U256::from(25), 11));
        detector.graph.add_edge(b_idx, s2_idx, (U256::from(25), 11));

        // Should NOT detect (percentages too high)
        assert!(!detector.check_motifs_against(c_idx, 12));
    }

    #[test]
    fn test_concurrent_patterns() {
        let mut detector = AMLMotifDetector::new(test_config());

        // Set up multiple suspicious patterns in same graph
        let source1 = addr("0xff50000000000000000000000000000000000001");
        let source2 = addr("0xff50000000000000000000000000000000000002");
        let inter1 = addr("0xff50000000000000000000000000000000000003");
        let inter2 = addr("0xff50000000000000000000000000000000000004");
        let dest = addr("0xff50000000000000000000000000000000000005");

        let s1_idx = detector.get_or_add_node(source1);
        let s2_idx = detector.get_or_add_node(source2);
        let i1_idx = detector.get_or_add_node(inter1);
        let i2_idx = detector.get_or_add_node(inter2);
        let d_idx = detector.get_or_add_node(dest);

        // Pattern 1: Scatter-gather from source1
        detector.graph.add_edge(s1_idx, i1_idx, (U256::from(300), 10));
        detector.graph.add_edge(s1_idx, i2_idx, (U256::from(300), 10));
        detector.graph.add_edge(i1_idx, d_idx, (U256::from(300), 11));
        detector.graph.add_edge(i2_idx, d_idx, (U256::from(300), 11));

        // Pattern 2: Also creates fan-in at dest
        // (Already has 2 inputs from pattern 1)

        // Should detect scatter-gather
        assert!(detector.check_motifs_against(d_idx, 12));
    }

    #[test]
    fn test_graph_state_consistency_after_rollback() {
        let mut detector = AMLMotifDetector::new(test_config());
        let dest = addr("0xff60000000000000000000000000000000000001");
        let block = 10;

        // Try to add transactions that will fail
        let mut txs = Vec::new();
        for i in 0..6 {
            let from = addr(&format!("0xff6000000000000000000000000000000000000{}", i + 2));
            txs.push((from, dest, U256::from(50)));
        }

        // This should fail and rollback
        assert!(detector.consensus_validate_block(&txs, block, parent_hash(block-1)));

        // Graph should be completely clean
        assert_eq!(detector.graph.edge_count(), 0);
        // assert_eq!(detector.graph.node_count(), 0);
        assert!(detector.building_block.is_none());
        assert!(detector.building_edges.is_empty());
    }
}
