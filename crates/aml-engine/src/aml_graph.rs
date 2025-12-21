use petgraph::stable_graph::{StableGraph, NodeIndex, EdgeIndex};
use petgraph::Direction::{Incoming};
use std::collections::{HashMap, HashSet, VecDeque};
use alloy_primitives::{Address, B256, U256};
use petgraph::Outgoing;
use rustc_hash::FxHashMap;

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
    pub fan_out_count_threshold: u64,
    pub fan_out_sum_threshold: U256,
}

#[derive(Clone, Debug)]
pub struct TransferEdge {
    pub amount: U256,
    pub block: u64,
    pub token: Address,
}

#[derive(Debug)]
struct EvalResult {
    edge_idx: EdgeIndex,
    from_idx: NodeIndex,
    to_idx: NodeIndex,
    from_created: bool,
    to_created: bool,
    suspicious_from: bool,
    suspicious_to: bool,
}

impl EvalResult {
    #[inline]
    fn suspicious(&self) -> bool {
        self.suspicious_from || self.suspicious_to
    }
}

/// ---------------------------------------------------------------------------
/// Main Detector
/// ---------------------------------------------------------------------------

pub struct AMLMotifDetector {
    pub graph: StableGraph<Address, TransferEdge>, // edge = (amount, block)
    pub node_map: FxHashMap<Address, NodeIndex>,

    pub per_block_edges: FxHashMap<u64, Vec<EdgeIndex>>,
    pub block_queue: VecDeque<u64>,

    // Track edges in order for current block building
    pub building_edges: Vec<EdgeIndex>,
    pub building_block: Option<(u64, B256)>,

    pub config: Config,
}

impl AMLMotifDetector {
    pub fn new(config: Config) -> Self {
        Self {
            graph: StableGraph::new(),
            node_map: FxHashMap::default(),
            per_block_edges: FxHashMap::default(),
            block_queue: VecDeque::new(),
            building_edges: Vec::new(),
            building_block: None,
            config,
        }
    }

    // --------------------------------------------------------------------
    // Node helpers
    // --------------------------------------------------------------------

    /// Returns true if the node was just created
    fn get_or_add_node(&mut self, addr: Address) -> (NodeIndex, bool) {
        if let Some(&idx) = self.node_map.get(&addr) {
            (idx, false)
        } else {
            let idx = self.graph.add_node(addr);
            self.node_map.insert(addr, idx);
            (idx, true)
        }
    }

    fn remove_node_created(&mut self, nidx: NodeIndex) {
        // obtain address (node weight is Address)
        if let Some(&addr) = self.graph.node_weight(nidx) {
            let _ = self.graph.remove_node(nidx);
            self.node_map.remove(&addr);
        } else {
            let _ = self.graph.remove_node(nidx);
        }
    }

    fn evaluate_edge_incremental(
        &mut self,
        token: Address,
        from: Address,
        to: Address,
        amount: U256,
        block: u64,
    ) -> EvalResult {
        let (from_idx, from_created) = self.get_or_add_node(from);
        let (to_idx, to_created) = self.get_or_add_node(to);

        // Tentatively add the edge so checks see it
        let edge_idx = self.graph.add_edge(from_idx, to_idx, TransferEdge{amount, block, token});

        // Evaluate motifs with the tentative edge present
        let suspicious_from = self.check_motifs_from(from_idx, block);
        let suspicious_to = self.check_motifs_against(to_idx, block);

        EvalResult {
            edge_idx,
            from_idx,
            to_idx,
            from_created,
            to_created,
            suspicious_from,
            suspicious_to,
        }
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
        token: Address,
        block: u64,
        parent_hash: B256,
    ) -> bool {
        if self.building_block != Some((block, parent_hash)) {
            self.reset_block_building();
            self.building_block = Some((block, parent_hash));
        }

        let res = self.evaluate_edge_incremental(token, from, to, amount, block);

        if res.suspicious() {
            // rollback: remove tentative edge
            let _ = self.graph.remove_edge(res.edge_idx);

            // remove only nodes created in this call
            if res.from_created { self.remove_node_created(res.from_idx); }
            if res.to_created   { self.remove_node_created(res.to_idx); }

            true // exclude tx
        } else {
            // keep edge; record for later clean reset or consensus re-validate
            self.building_edges.push(res.edge_idx);
            false
        }
    }

    // --------------------------------------------------------------------
    // CONSENSUS VALIDATION: Validators check complete blocks
    // --------------------------------------------------------------------
    /// Called during consensus to validate an entire block.
    /// Works for both proposers (who have building_edges) and validators (who don't).
    /// Returns `true` if any tx creates a forbidden motif.
    pub fn consensus_validate_block(
        &mut self,
        txs: &[(Address, Address, Address, U256)], // token sender receiver amount
        block: u64,
        parent_hash: B256,
    ) -> bool {
        let is_self_built = self
            .building_block
            .as_ref()
            .map(|(b, p)| *b == block && *p == parent_hash)
            .unwrap_or(false);

        // For self-built blocks, remove building_edges so we can re-validate cleanly
        if is_self_built {
            for eidx in self.building_edges.drain(..) {
                self.graph.remove_edge(eidx);
            }
            self.building_block = None;
        }

        // Validate all transactions incrementally
        let mut temp_edges: Vec<EvalResult> = Vec::new();


        for &(token, from, to, amount) in txs {
            let res = self.evaluate_edge_incremental(token, from, to, amount, block);

            if res.suspicious() {
                // rollback the current edge
                let _ = self.graph.remove_edge(res.edge_idx);
                if res.from_created { self.remove_node_created(res.from_idx); }
                if res.to_created   { self.remove_node_created(res.to_idx); }

                // rollback all accumulated temp edges
                for prev in temp_edges.drain(..) {
                    let _ = self.graph.remove_edge(prev.edge_idx);
                    if prev.from_created { self.remove_node_created(prev.from_idx); }
                    if prev.to_created   { self.remove_node_created(prev.to_idx); }
                }

                return true; // block contains prohibited motif
            } else {
                temp_edges.push(res);
            }
        }

        // Success path: remove all temp edges and nodes created for validation only
        for res in temp_edges.drain(..) {
            let _ = self.graph.remove_edge(res.edge_idx);
            if res.from_created { self.remove_node_created(res.from_idx); }
            if res.to_created   { self.remove_node_created(res.to_idx); }
        }

        false
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
        all_txs: &[(Address, Address, Address, U256)],
        successful_indices: &[usize],
    ) {
        // Add edges for successful transactions (if any)
        if !successful_indices.is_empty() {
            let mut block_edges = Vec::new();
            for &idx in successful_indices {
                if let Some(&(token, from, to, amount)) = all_txs.get(idx) {
                    let (from_idx, from_created) = self.get_or_add_node(from);
                    let (to_idx, to_created) = self.get_or_add_node(to);
                    let eidx = self.graph.add_edge(from_idx, to_idx, TransferEdge{amount, block, token});
                    block_edges.push(eidx);
                }
            }
            self.per_block_edges.insert(block, block_edges);
            self.block_queue.push_back(block);
        }

        // Clear building state
        self.building_edges.clear();
        self.building_block = None;

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
        // This should never happen (reverting a block that's still being built)
        if let Some((building_blk, _)) = self.building_block {
            if reverted.contains(&building_blk) {
                for eidx in self.building_edges.drain(..) {
                    self.graph.remove_edge(eidx);
                }
                self.building_block = None;
            }
        }

        for &blk in reverted {
            if let Some(edge_idxs) = self.per_block_edges.remove(&blk) {
                for eidx in edge_idxs {
                    self.graph.remove_edge(eidx);
                }
            }
            self.block_queue.retain(|&b| b != blk);
        }
    }

    fn check_motifs_against(&self, to_idx: NodeIndex, current_block: u64) -> bool {
        // 1. Fan-in: Multiple distinct senders to one address
        let mut fan_in_count = 0u64;
        let mut fan_in_sum = U256::from(0);
        let mut seen = HashSet::new();

        // TODO: Check if we should limit how many nodes to look at in total using .take(NUMBER_OF_NODES)
        for neighbor in self.graph.neighbors_directed(to_idx, Incoming) {
            if !seen.insert(neighbor) {
                continue; // Already processed this neighbor
            }

            // Sum ALL edges from this neighbor within the window
            let mut neighbor_total = U256::from(0);
            for edge_ref in self.graph.edges_connecting(neighbor, to_idx) {
                let edge = edge_ref.weight();

                if current_block >= edge.block && current_block - edge.block <= self.config.window_blocks {
                    neighbor_total += edge.amount;
                }
            }

            if neighbor_total > U256::ZERO {
                fan_in_count += 1;
                fan_in_sum += neighbor_total;
                if fan_in_count > self.config.fan_in_count_threshold
                    || fan_in_sum > self.config.fan_in_sum_threshold
                {
                    println!("Fan_in_count or fan_in_sum exceeded");
                    return true;
                }
            }
        }

        // 2. Scatter-Gather: single source → multiple intermediaries → to_idx
        // Pattern: One source splits funds through 2+ intermediaries that converge at destination
        let mut source_data = HashMap::<NodeIndex, (HashSet<NodeIndex>, U256)>::new();

        for inter in self.graph.neighbors_directed(to_idx, Incoming) {
            // Calculate time window for intermediary → destination
            let mut inter_to_dest_max_block = 0u64;
            let mut inter_to_dest_sum = U256::from(0);

            for edge_ref in self.graph.edges_connecting(inter, to_idx) {
                let edge = edge_ref.weight();
                if current_block >= edge.block && current_block - edge.block <= self.config.window_blocks {
                    inter_to_dest_sum += edge.amount;
                    inter_to_dest_max_block = inter_to_dest_max_block.max(edge.block);
                }
            }

            if inter_to_dest_sum == U256::ZERO {
                continue;
            }

            // Look at sources feeding this intermediary
            for src in self.graph.neighbors_directed(inter, Incoming) {
                // Calculate time window for source → intermediary
                let mut src_to_inter_max_block = 0u64;
                let mut src_to_inter_sum = U256::from(0);

                for edge_ref in self.graph.edges_connecting(src, inter) {
                    let edge = edge_ref.weight();
                    if current_block >= edge.block && current_block - edge.block <= self.config.window_blocks {
                        src_to_inter_sum += edge.amount;
                        src_to_inter_max_block = src_to_inter_max_block.max(edge.block);
                    }
                }

                if src_to_inter_sum == U256::ZERO {
                    continue;
                }

                // Check temporal ordering: latest source→inter must be before or at latest inter→dest
                // This ensures source sent to intermediary before intermediary forwarded to dest
                if src_to_inter_max_block <= inter_to_dest_max_block {
                    // Calculate bottleneck flow for this path
                    let bottleneck = src_to_inter_sum.min(inter_to_dest_sum);

                    let entry = source_data.entry(src).or_insert((HashSet::new(), U256::from(0)));
                    entry.0.insert(inter); // Track which intermediary
                    entry.1 += bottleneck; // Accumulate total flow from this source
                }
            }
        }

        // Check if any source used 2+ intermediaries with significant total flow
        for (_src, (intermediaries, total_flow)) in source_data.iter() {
            if intermediaries.len() >= 2 && *total_flow > self.config.scatter_gather_threshold {
                println!("Scatter-gather pattern");
                return true;
            }
        }

        false
    }

    /// Checks sender-centric motifs for AML patterns.
    /// Returns true if any suspicious pattern is detected.
    fn check_motifs_from(&self, from_idx: NodeIndex, current_block: u64) -> bool {
        // 1. Fan-Out (Dispersal): Single sender → multiple distinct receivers
        let mut fan_out_count = 0u64;
        let mut fan_out_sum = U256::from(0);
        let mut seen = HashSet::new();

        for neighbor in self.graph.neighbors_directed(from_idx, Outgoing) {
            if !seen.insert(neighbor) {
                continue;
            }

            let mut neighbor_total = U256::from(0);
            for edge_ref in self.graph.edges_connecting(from_idx, neighbor) {
                let edge = edge_ref.weight();
                if current_block >= edge.block && current_block - edge.block <= self.config.window_blocks {
                    neighbor_total += edge.amount;
                }
            }

            if neighbor_total > U256::ZERO {
                fan_out_count += 1;
                fan_out_sum += neighbor_total;
                if fan_out_count > self.config.fan_out_count_threshold
                    || fan_out_sum > self.config.fan_out_sum_threshold
                {
                    println!("Fan-out count or sum exceeded");
                    return true;
                }
            }
        }

        // 2. Gather-scatter (hub detection)
        // Pattern: Multiple sources → from_idx → receiver (from_idx acts as mixing hub)
        let mut receiver_data = HashMap::<NodeIndex, (HashSet<NodeIndex>, U256)>::new();

        for source in self.graph.neighbors_directed(from_idx, Incoming) {
            // Calculate time window for source → sender (from_idx)
            let mut source_to_sender_max_block = 0u64;
            let mut source_to_sender_sum = U256::from(0);

            for edge_ref in self.graph.edges_connecting(source, from_idx) {
                let edge = edge_ref.weight();
                if current_block >= edge.block && current_block - edge.block <= self.config.window_blocks {
                    source_to_sender_sum += edge.amount;
                    source_to_sender_max_block = source_to_sender_max_block.max(edge.block);
                }
            }

            if source_to_sender_sum == U256::ZERO {
                continue;
            }

            // Look at receivers from the sender
            for recv in self.graph.neighbors_directed(from_idx, Outgoing) {
                // Calculate time window for sender (from_idx) → receiver
                let mut sender_to_recv_max_block = 0u64;
                let mut sender_to_recv_sum = U256::from(0);

                for edge_ref in self.graph.edges_connecting(from_idx, recv) {
                    let edge = edge_ref.weight();
                    if current_block >= edge.block && current_block - edge.block <= self.config.window_blocks {
                        sender_to_recv_sum += edge.amount;
                        sender_to_recv_max_block = sender_to_recv_max_block.max(edge.block);
                    }
                }

                if sender_to_recv_sum == U256::ZERO {
                    continue;
                }

                // Check temporal ordering: latest source→sender must be before or at latest sender→recv
                if source_to_sender_max_block <= sender_to_recv_max_block {
                    let bottleneck = source_to_sender_sum.min(sender_to_recv_sum);

                    let entry = receiver_data.entry(recv).or_insert((HashSet::new(), U256::from(0)));
                    entry.0.insert(source); // Track which source
                    entry.1 += bottleneck;
                }
            }
        }

        // Check if any receiver gets funds from 2+ sources through this sender
        for (_recv, (sources, total_flow)) in receiver_data.iter() {
            if sources.len() >= 2 && *total_flow > self.config.gather_scatter_threshold {
                println!("Gather-scatter pattern (hub behavior)");
                return true;
            }
        }

        false
    }

    // --------------------------------------------------------------------
    // ROLLING PRUNE
    // --------------------------------------------------------------------

    /// Prunes edges outside the block window and removes orphaned nodes
    fn prune(&mut self, current_block: u64) {
        let nodes_before = self.graph.node_count();
        let edges_before = self.graph.edge_count();

        while let Some(&old) = self.block_queue.front() {
            if current_block - old <= self.config.window_blocks {
                break;
            }
            self.block_queue.pop_front();
            if let Some(edges) = self.per_block_edges.remove(&old) {
                let mut orphan_candidates = HashSet::new();
                for eidx in edges {
                    if let Some((source, target)) = self.graph.edge_endpoints(eidx) {
                        orphan_candidates.insert(source);
                        orphan_candidates.insert(target);
                    }
                    self.graph.remove_edge(eidx);
                }
                let mut removed = 0;
                for node in orphan_candidates {
                    if self.graph.neighbors_directed(node, Incoming).count() == 0
                        && self.graph.neighbors_directed(node, Outgoing).count() == 0
                    {
                        if let Some(node_addr) = self.graph.node_weight(node) {
                            self.node_map.remove(node_addr);
                        }
                        self.graph.remove_node(node);
                        removed += 1;
                    }
                }
            }
        }

        println!("Prune complete: nodes {} -> {}, edges {} -> {}",
                 nodes_before, self.graph.node_count(),
                 edges_before, self.graph.edge_count());
    }

    pub fn estimate_internal_memory(&self) -> usize {
        let node_map_size = self.node_map.capacity() * (std::mem::size_of::<Address>() + std::mem::size_of::<NodeIndex>());
        let graph_nodes = self.graph.node_count() * std::mem::size_of::<Address>();
        // Edges in petgraph StableGraph store (amount, block) + internal pointers/indices
        let graph_edges = self.graph.edge_count() * (std::mem::size_of::<(U256, u64)>() + 32);

        node_map_size + graph_nodes + graph_edges
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256};
    use std::str::FromStr;

    pub const ZERO_ADDRESS: Address = Address::ZERO;

    fn addr(hex: &str) -> Address {
        Address::from_str(hex).unwrap()
    }
    fn parent_hash(block: u64) -> B256 {
        let mut bytes = [0u8; 32];
        bytes[24..].copy_from_slice(&block.to_be_bytes());
        B256::from(bytes)
    }
    fn cfg() -> Config {
        Config {
            window_blocks: 5,
            fan_in_count_threshold: 3,
            fan_in_sum_threshold: U256::from(10),
            scatter_gather_threshold: U256::from(8),
            gather_scatter_threshold: U256::from(8),
            fan_out_count_threshold: 3,
            fan_out_sum_threshold: U256::from(10),
        }
    }

    // -----------------------------
    // 1) AML motifs: fan-in & fan-out
    // -----------------------------
    #[test]
    fn aml_fan_in_and_fan_out_basic() {
        let mut d = AMLMotifDetector::new(cfg());
        let a1 = addr("0x1000000000000000000000000000000000000001");
        let a2 = addr("0x1000000000000000000000000000000000000002");
        let sink = addr("0x10000000000000000000000000000000000000ff");

        // FAN-IN: 2 senders within window, total 12 > 10 -> suspicious
        assert!(!d.proposer_check_tx(a1, sink, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d.proposer_check_tx(a2, sink, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(d.proposer_check_tx(addr("0x1000000000000000000000000000000000000003"), sink, U256::from(1), ZERO_ADDRESS, 10, parent_hash(9)));

        // FAN-OUT: one sender dispersing to multiple recipients, total > threshold
        let mut d2 = AMLMotifDetector::new(cfg());
        let src = addr("0x2000000000000000000000000000000000000001");
        let r1  = addr("0x2000000000000000000000000000000000000002");
        let r2  = addr("0x2000000000000000000000000000000000000003");
        assert!(!d2.proposer_check_tx(src, r1, U256::from(6), ZERO_ADDRESS, 10, parent_hash(9)));
        // Next edge causes fan-out count >= 2 and sum 12 > 10 -> suspicious
        assert!( d2.proposer_check_tx(src, r2, U256::from(6), ZERO_ADDRESS, 10, parent_hash(9)));
    }

    // --------------------------------
    // 2) Scatter-gather & Gather-scatter
    // --------------------------------
    #[test]
    fn aml_scatter_gather_and_gather_scatter() {
        let mut d = AMLMotifDetector::new(cfg());
        let source = addr("0x3000000000000000000000000000000000000001");
        let i1     = addr("0x3000000000000000000000000000000000000002");
        let i2     = addr("0x3000000000000000000000000000000000000003");
        let sink   = addr("0x30000000000000000000000000000000000000aa");

        // Scatter-gather: source -> i1 -> sink, source -> i2 -> sink
        assert!(!d.proposer_check_tx(source, i1, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d.proposer_check_tx(i1, sink, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d.proposer_check_tx(source, i2, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        // This final edge should trigger (bottlenecks sum to 10 > 8)
        assert!( d.proposer_check_tx(i2, sink, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));

        // Gather-scatter (hub): multiple sources -> hub -> one receiver
        let mut d2 = AMLMotifDetector::new(cfg());
        let s1 = addr("0x4000000000000000000000000000000000000001");
        let s2 = addr("0x4000000000000000000000000000000000000002");
        let hub = addr("0x40000000000000000000000000000000000000bb");
        let recv = addr("0x40000000000000000000000000000000000000bc");
        assert!(!d2.proposer_check_tx(s1, hub, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d2.proposer_check_tx(s2, hub, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        // Hub to receiver (sum bottlenecks = 10 > threshold 8)
        assert!( d2.proposer_check_tx(hub, recv, U256::from(10), ZERO_ADDRESS, 10, parent_hash(9)));
    }

    // --------------------------------
    // 3) Consensus validation rollback
    // --------------------------------
    #[test]
    fn consensus_rollback_on_suspicious_block() {
        let mut d = AMLMotifDetector::new(cfg());
        let sink = addr("0x50000000000000000000000000000000000000ff");
        let block = 20;
        // 3 senders -> sink to exceed count threshold (2)
        let txs: Vec<_> = (0..3).map(|i| {
            (ZERO_ADDRESS, addr(&format!("0xf10000000000000000000000000000000000000{}", i + 2)),
             sink,
             U256::from(5))
        })
            .collect();
        assert!(d.consensus_validate_block(&txs, block, parent_hash(block-1)));
        // All temp edges rolled back
        assert_eq!(d.graph.edge_count(), 0);
        assert!(d.building_block.is_none());
        assert!(d.building_edges.is_empty());
    }

    // --------------------------------
    // 4) Pruning: edges removed when outside window
    // --------------------------------
    #[test]
    fn pruning_removes_old_edges() {
        let mut d = AMLMotifDetector::new(cfg());
        let a = addr("0x6000000000000000000000000000000000000001");
        let b = addr("0x6000000000000000000000000000000000000002");

        // Commit blocks 0..=6 (window_blocks=5 -> keeps blocks 1..=6 at current_block=6)
        for blk in 0..=6 {
            let txs = vec![(ZERO_ADDRESS, a, b, U256::from(1))];
            let parent = parent_hash(0);
            let idx: Vec<usize> = (0..txs.len()).collect();
            assert!(!d.consensus_validate_block(&txs, blk, parent));
            d.block_commit(blk, parent, &txs, &idx);
        }
        // Inclusive boundary: blocks 1..=6 remain -> 6 edges
        assert_eq!(d.graph.edge_count(), 6);
    }


    // -------------------------------------------------------------
    // 5) Nodes pruned when orphaned
    // -------------------------------------------------------------
    // #[test]
    // fn pruning_removes_orphan_nodes() {
    //     let mut d = AMLMotifDetector::new(cfg());
    //     let a = addr("0x7000000000000000000000000000000000000001");
    //     let b = addr("0x7000000000000000000000000000000000000002");
    //
    //     // Commit a single block with one edge
    //     let txs = vec![(a,b,U256::from(1))];
    //     let idx: Vec<usize> = (0..txs.len()).collect();
    //     assert!(!d.consensus_validate_block(&txs, 10, parent_hash(9)));
    //     d.block_commit(10, parent_hash(9), &txs, &idx);
    //
    //     // Advance far enough to prune block 10
    //     let dummy = vec![(addr("0x70000000000000000000000000000000000000aa"),
    //                       addr("0x70000000000000000000000000000000000000ab"),
    //                       U256::from(1))];
    //     let di: Vec<usize> = (0..dummy.len()).collect();
    //     assert!(!d.consensus_validate_block(&dummy, 16, parent_hash(15)));
    //     d.block_commit(16, parent_hash(15), &dummy, &di);
    //
    //     // After pruning, both a and b should be removed (orphaned)
    //     assert_eq!(d.graph.node_count(), 2, "If this fails, enable when orphan removal is implemented");
    // }
}
