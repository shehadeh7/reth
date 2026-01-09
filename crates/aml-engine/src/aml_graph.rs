use petgraph::stable_graph::{StableGraph, NodeIndex, EdgeIndex};
use petgraph::Direction::{Incoming};
use std::collections::{HashMap, HashSet, VecDeque};
use alloy_primitives::{Address, B256, U256};
use petgraph::Outgoing;
use rustc_hash::{FxHashMap, FxHashSet};

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
}

#[derive(Default, Clone)]
struct BlockCaches {
    /// Base-graph window sums for (a,b) -> (sum, max_block) at current_block.
    base_pair_sum: FxHashMap<(Address, Address), (U256, u64)>,

    /// Cached neighbors per address (union of base graph + overlay so far).
    /// These grow incrementally as overlay grows; never shrink during block.
    neighbors_in: FxHashMap<Address, FxHashSet<Address>>,
    neighbors_out: FxHashMap<Address, FxHashSet<Address>>,
}

impl BlockCaches {
    #[inline]
    fn clear(&mut self) {
        self.base_pair_sum.clear();
        self.neighbors_in.clear();
        self.neighbors_out.clear();
    }
}

#[derive(Default, Clone)]
struct BlockOverlay {
    // sender -> [(receiver, edge), ...]
    outgoing_pairs: FxHashMap<Address, Vec<(Address, TransferEdge)>>,
    // receiver -> [(sender, edge), ...]
    incoming_pairs: FxHashMap<Address, Vec<(Address, TransferEdge)>>,
    // Fast path: aggregated by (from,to) for O(1) lookup
    // (sum of amounts within overlay block; max block height of contributions)
    pair_sum: FxHashMap<(Address, Address), (U256, u64)>,
}

impl BlockOverlay {
    #[inline]
    fn clear(&mut self) {
        self.outgoing_pairs.clear();
        self.incoming_pairs.clear();
        self.pair_sum.clear();
    }

    #[inline]
    fn append(&mut self, from: Address, to: Address, edge: TransferEdge) {
        // Update aggregate
        let entry = self.pair_sum.entry((from, to)).or_insert((U256::ZERO, 0));
        entry.0 += edge.amount;
        entry.1 = entry.1.max(edge.block);

        // Keep detailed per-edge records if needed
        self.outgoing_pairs.entry(from).or_default().push((to, edge.clone()));
        self.incoming_pairs.entry(to).or_default().push((from, edge));
    }

    #[inline]
    fn outgoing_slice(&self, from: &Address) -> &[(Address, TransferEdge)] {
        self.outgoing_pairs.get(from).map(|v| v.as_slice()).unwrap_or(&[])
    }

    #[inline]
    fn incoming_slice(&self, to: &Address) -> &[(Address, TransferEdge)] {
        self.incoming_pairs.get(to).map(|v| v.as_slice()).unwrap_or(&[])
    }

    #[inline]
    fn overlay_pair(&self, a: Address, b: Address) -> (U256, u64) {
        self.pair_sum.get(&(a, b)).copied().unwrap_or((U256::ZERO, 0))
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
    pub building_block: Option<(u64, B256)>,

    pub config: Config,

    // Block-scoped overlay for proposal & consensus validation
    overlay: BlockOverlay,

    // Block-scoped caches for neighbors and base pair sums
    block_caches: BlockCaches,
}

impl AMLMotifDetector {
    pub fn new(config: Config) -> Self {
        Self {
            graph: StableGraph::new(),
            node_map: FxHashMap::default(),
            per_block_edges: FxHashMap::default(),
            block_queue: VecDeque::new(),
            building_block: None,
            config,
            overlay: BlockOverlay::default(),
            block_caches: BlockCaches::default(),
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

    // ----------------------------------------------------------------------------
    // Core cache operations (build incrementally, never rebuild within the block)
    // ----------------------------------------------------------------------------
    /// Ensure neighbors for addr/dir are cached
    #[inline]
    fn ensure_neighbors_cached(&mut self, addr: Address, dir: petgraph::Direction) {
        let map = match dir {
            Incoming => &mut self.block_caches.neighbors_in,
            Outgoing => &mut self.block_caches.neighbors_out,
        };
        if map.contains_key(&addr) {
            return; // Already cached
        }

        let mut set = FxHashSet::default();

        // Base graph neighbors
        if let Some(&nidx) = self.node_map.get(&addr) {
            for n in self.graph.neighbors_directed(nidx, dir) {
                if let Some(&a) = self.graph.node_weight(n) {
                    set.insert(a);
                }
            }
        }

        // Overlay neighbors (as of now)
        match dir {
            Outgoing => {
                for (to, _e) in self.overlay.outgoing_slice(&addr) {
                    set.insert(*to);
                }
            }
            Incoming => {
                for (from, _e) in self.overlay.incoming_slice(&addr) {
                    set.insert(*from);
                }
            }
        }

        map.insert(addr, set);
    }

    /// Get cached neighbors (ensure_* must be called first!)
    #[inline]
    fn get_neighbors_cached(&self, addr: Address, dir: petgraph::Direction) -> &FxHashSet<Address> {
        let map = match dir {
            Incoming => &self.block_caches.neighbors_in,
            Outgoing => &self.block_caches.neighbors_out,
        };
        map.get(&addr).expect("neighbors not cached")
    }

    /// Update neighbor caches when overlay grows (incremental insert; unconditional)
    #[inline]
    fn update_neighbor_cache_for_edge(&mut self, from: Address, to: Address) {
        self.block_caches.neighbors_out.entry(from).or_default().insert(to);
        self.block_caches.neighbors_in.entry(to).or_default().insert(from);
    }

    /// Base-graph window sum (cached per block)
    #[inline]
    fn base_pair_sum_cached(&mut self, a: Address, b: Address, current_block: u64) -> (U256, u64) {
        if let Some(v) = self.block_caches.base_pair_sum.get(&(a, b)) {
            return *v;
        }

        let mut sum = U256::ZERO;
        let mut maxb = 0u64;

        if let (Some(&ai), Some(&bi)) = (self.node_map.get(&a), self.node_map.get(&b)) {
            for e in self.graph.edges_connecting(ai, bi) {
                let w = e.weight();
                if current_block >= w.block && current_block - w.block < self.config.window_blocks {
                    sum += w.amount;
                    maxb = maxb.max(w.block);
                }
            }
        }

        let v = (sum, maxb);
        self.block_caches.base_pair_sum.insert((a, b), v);
        v
    }

    /// Full window sum: base + overlay + ephemeral
    #[inline]
    fn window_sum_full(
        &mut self,
        a: Address,
        b: Address,
        current_block: u64,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
    ) -> (U256, u64) {
        let (mut sum, mut maxb) = self.base_pair_sum_cached(a, b, current_block);

        // Overlay contribution
        let (osum, omax) = self.overlay.overlay_pair(a, b);
        if omax != 0 && current_block >= omax && current_block - omax < self.config.window_blocks {
            sum += osum;
            maxb = maxb.max(omax);
        }

        // Ephemeral "what-if"
        if let Some((ea, eb, ew)) = ephemeral {
            if ea == a && eb == b
                && current_block >= ew.block
                && current_block - ew.block < self.config.window_blocks
            {
                sum += ew.amount;
                maxb = maxb.max(ew.block);
            }
        }

        (sum, maxb)
    }

    /// Helper: copy neighbors into a local Vec and inject ephemeral neighbor (borrow-safe)
    #[inline]
    fn neighbors_to_vec_with_ephemeral(
        &mut self,
        addr: Address,
        dir: petgraph::Direction,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
        out: &mut Vec<Address>,
    ) {
        self.ensure_neighbors_cached(addr, dir);
        out.clear();
        let cached = self.get_neighbors_cached(addr, dir);
        out.reserve(cached.len().saturating_sub(out.capacity()));
        out.extend(cached.iter().copied());

        if let Some((efrom, eto, _)) = ephemeral {
            match dir {
                Incoming if eto == addr => {
                    if !out.contains(&efrom) {
                        out.push(efrom);
                    }
                }
                Outgoing if efrom == addr => {
                    if !out.contains(&eto) {
                        out.push(eto);
                    }
                }
                _ => {}
            }
        }
    }

    // ----------------------------------------------------------------------------
    // Motif checks using cached neighbors
    // ----------------------------------------------------------------------------
    /// Receiver-centric motifs: fan-in & scatter-gather
    fn check_motifs_against_view_ephemeral(
        &mut self,
        to_addr: Address,
        current_block: u64,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
    ) -> bool {
        // 1) FAN-IN
        let mut sources = Vec::new();
        self.neighbors_to_vec_with_ephemeral(to_addr, Incoming, ephemeral, &mut sources);

        let mut fan_in_count = 0u64;
        let mut fan_in_sum = U256::ZERO;

        for src_addr in sources.into_iter() {
            let (neighbor_total, _maxb) =
                self.window_sum_full(src_addr, to_addr, current_block, ephemeral);
            if neighbor_total > U256::ZERO {
                fan_in_count += 1;
                fan_in_sum += neighbor_total;
                if fan_in_count > self.config.fan_in_count_threshold
                    || fan_in_sum > self.config.fan_in_sum_threshold
                {
                    // println!("fan in detected");
                    return true;
                }
            }
        }

        // 2) SCATTER-GATHER
        let mut intermediaries = Vec::new();
        self.neighbors_to_vec_with_ephemeral(to_addr, Incoming, ephemeral, &mut intermediaries);

        let mut source_data: FxHashMap<Address, (FxHashSet<Address>, U256)> = FxHashMap::default();

        for inter_addr in intermediaries.into_iter() {
            let (inter_to_dest_sum, inter_to_dest_max) =
                self.window_sum_full(inter_addr, to_addr, current_block, ephemeral);
            if inter_to_dest_sum == U256::ZERO {
                continue;
            }

            let mut srcs = Vec::new();
            self.neighbors_to_vec_with_ephemeral(inter_addr, Incoming, None, &mut srcs);

            for src_addr in srcs.into_iter() {
                let (src_to_inter_sum, src_to_inter_max) =
                    self.window_sum_full(src_addr, inter_addr, current_block, ephemeral);
                if src_to_inter_sum == U256::ZERO {
                    continue;
                }

                // Temporal ordering
                if src_to_inter_max <= inter_to_dest_max {
                    let bottleneck = src_to_inter_sum.min(inter_to_dest_sum);
                    let entry = source_data
                        .entry(src_addr)
                        .or_insert((FxHashSet::default(), U256::ZERO));
                    entry.0.insert(inter_addr);
                    entry.1 += bottleneck;
                }
            }
        }

        for (_src, (inter_set, total_flow)) in source_data.into_iter() {
            if inter_set.len() >= 2 && total_flow > self.config.scatter_gather_threshold {
                // println!("scatter gather detected");
                return true;
            }
        }

        false
    }

    /// Sender-centric motifs: fan-out & gather-scatter (hub behavior)
    fn check_motifs_from_view_ephemeral(
        &mut self,
        from_addr: Address,
        current_block: u64,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
    ) -> bool {
        // 1) FAN-OUT
        let mut destinations = Vec::new();
        self.neighbors_to_vec_with_ephemeral(from_addr, Outgoing, ephemeral, &mut destinations);

        let mut fan_out_count = 0u64;
        let mut fan_out_sum = U256::ZERO;

        for recv_addr in destinations.into_iter() {
            let (neighbor_total, _maxb) =
                self.window_sum_full(from_addr, recv_addr, current_block, ephemeral);
            if neighbor_total > U256::ZERO {
                fan_out_count += 1;
                fan_out_sum += neighbor_total;
                if fan_out_count > self.config.fan_out_count_threshold
                    || fan_out_sum > self.config.fan_out_sum_threshold
                {
                    // println!("Fan out detected");
                    return true;
                }
            }
        }

        // 2) GATHER-SCATTER (hub): multiple sources → from_addr → one receiver
        let mut sources = Vec::new();
        self.neighbors_to_vec_with_ephemeral(from_addr, Incoming, ephemeral, &mut sources);

        let mut incoming_sum = U256::ZERO;
        for src_addr in sources.into_iter() {
            let (sum, _maxb) = self.window_sum_full(src_addr, from_addr, current_block, ephemeral);
            incoming_sum += sum;
        }

        let flow_volume = incoming_sum.min(fan_out_sum);
        if flow_volume > self.config.gather_scatter_threshold {
            // println!("gather scatter detected");
            return true;
        }

        false
    }

    // ----------------------------------------------------------------------------
    // “Would this tx be suspicious?” (evaluate-first, no mutation)
    // ----------------------------------------------------------------------------
    fn would_be_suspicious(
        &mut self,
        _token: Address,
        from: Address,
        to: Address,
        amount: U256,
        block: u64,
    ) -> (bool, bool) {
        let edge = TransferEdge { amount, block };
        let ephemeral = Some((from, to, &edge));
        let suspicious_from = self.check_motifs_from_view_ephemeral(from, block, ephemeral);
        let suspicious_to = self.check_motifs_against_view_ephemeral(to, block, ephemeral);
        (suspicious_from, suspicious_to)
    }

    // ----------------------------------------------------------------------------
    // BLOCK BUILDING: Proposer checks each tx during selection
    // ----------------------------------------------------------------------------
    /// Returns `true` if the tx is suspicious and should be excluded.
    /// If clean, we append it to the overlay and update caches so later txs see updated context.
    pub fn proposer_check_tx(
        &mut self,
        from: Address,
        to: Address,
        amount: U256,
        token: Address,
        block: u64,
        parent_hash: B256,
    ) -> bool {
        // Start/continue block-scoped caches
        if self.building_block != Some((block, parent_hash)) {
            self.block_caches.clear();
            self.overlay.clear();
            self.building_block = Some((block, parent_hash));
        }

        let (suspicious_from, suspicious_to) =
            self.would_be_suspicious(token, from, to, amount, block);
        if suspicious_from || suspicious_to {
            true
        } else {
            // Clean: append to overlay & update neighbor caches
            self.overlay.append(from, to, TransferEdge { amount, block });
            self.update_neighbor_cache_for_edge(from, to);
            false
        }
    }

    // ----------------------------------------------------------------------------
    // CONSENSUS VALIDATION: Validators check complete blocks
    // ----------------------------------------------------------------------------
    /// Returns vector of illicit tx indices. Clean txs get appended to overlay incrementally.
    pub fn consensus_validate_block(
        &mut self,
        txs: &[ (Address, Address, Address, U256) ], // token, sender, receiver, amount
        block: u64,
        parent_hash: B256,
    ) -> Vec<usize> {
        self.block_caches.clear();
        self.overlay.clear();

        let mut illicit_indices = Vec::new();

        for (idx, &(token, from, to, amount)) in txs.iter().enumerate() {
            let (suspicious_from, suspicious_to) =
                self.would_be_suspicious(token, from, to, amount, block);
            if suspicious_from || suspicious_to {
                illicit_indices.push(idx);
            } else {
                self.overlay.append(from, to, TransferEdge { amount, block });
                self.update_neighbor_cache_for_edge(from, to);
            }
        }

        self.block_caches.clear();
        self.overlay.clear();
        illicit_indices
    }

    // ----------------------------------------------------------------------------
    // BLOCK COMMIT
    // ----------------------------------------------------------------------------
    /// Called after a block is successfully committed.
    /// successful_txs: all successful transactions in block (in order)
    pub fn block_commit(
        &mut self,
        block: u64,
        _parent_hash: B256,
        successful_txs: &[ (Address, Address, Address, U256) ],
    ) {
        // Aggregate transfers between same pairs in this block
        if !successful_txs.is_empty() {
            let mut aggregated: FxHashMap<(Address, Address, Address), U256> = FxHashMap::default();
            for &(token, from, to, amount) in successful_txs {
                aggregated
                    .entry((token, from, to))
                    .and_modify(|total| *total += amount)
                    .or_insert(amount);
            }

            let mut block_edges = Vec::with_capacity(aggregated.len());
            for ((_token, from, to), aggregated_amount) in aggregated {
                let (from_idx, _) = self.get_or_add_node(from);
                let (to_idx, _) = self.get_or_add_node(to);
                let eidx = self.graph.add_edge(
                    from_idx,
                    to_idx,
                    TransferEdge { amount: aggregated_amount, block }
                );
                block_edges.push(eidx);
            }
            self.per_block_edges.insert(block, block_edges);
            self.block_queue.push_back(block);
        }

        self.overlay.clear();
        self.building_block = None;
        self.block_caches.clear();
        self.prune(block);
    }

    // ----------------------------------------------------------------------------
    // BLOCK BUILDING RESET
    // ----------------------------------------------------------------------------
    /// Called when block building is abandoned.
    pub fn reset_block_building(&mut self) {
        self.overlay.clear();
        self.building_block = None;
        self.block_caches.clear();
    }

    // ------------------------------------------
    // REORG HANDLING
    // ------------------------------------------
    pub fn reorg_revert(&mut self, reverted: &[u64]) {
        // This should never happen (reverting a block that's still being built)
        if let Some((building_blk, _)) = self.building_block {
            if reverted.contains(&building_blk) {
                self.overlay.clear();
                self.building_block = None;
            }
        }

        let mut edges_to_remove = Vec::new();
        let mut orphan_candidates = FxHashSet::default();

        for &blk in reverted {
            if let Some(edge_idxs) = self.per_block_edges.remove(&blk) {
                for eidx in &edge_idxs {
                    // Collect endpoints before removing edge
                    if let Some((source, target)) = self.graph.edge_endpoints(*eidx) {
                        orphan_candidates.insert(source);
                        orphan_candidates.insert(target);
                    }
                }
                edges_to_remove.extend(edge_idxs);
            }
        }

        for eidx in edges_to_remove {
            self.graph.remove_edge(eidx);
        }

        // Clean up block queue
        self.block_queue.retain(|&b| !reverted.contains(&b));

        // Remove orphaned nodes
        if !orphan_candidates.is_empty() {
            let removed = self.orphan_node_removal(orphan_candidates);
            println!("Reorg: removed {} orphaned nodes", removed);
        }
    }

    /// Execute a reorg with three distinct cases handled separately
    pub fn execute_reorg(
        &mut self,
        blocks_in_both: &[u64],
        blocks_only_in_old: &[u64],
        blocks_only_in_new: &[u64],
        new_blocks_map: &HashMap<u64, &(u64, B256, Vec<(Address, Address, Address, U256)>)>,
    ) {
        println!(
            "Executing reorg: {} blocks in both, {} only in old, {} only in new",
            blocks_in_both.len(),
            blocks_only_in_old.len(),
            blocks_only_in_new.len()
        );

        let mut total_orphan_candidates = FxHashSet::default();

        // Phase 1: Handle blocks in BOTH old and new (update edges)
        for &block in blocks_in_both {
            // Remove old edges for this block
            if let Some(old_edges) = self.per_block_edges.remove(&block) {
                for eidx in old_edges {
                    if let Some((source, target)) = self.graph.edge_endpoints(eidx) {
                        total_orphan_candidates.insert(source);
                        total_orphan_candidates.insert(target);
                    }
                    self.graph.remove_edge(eidx);
                }
            }

            // Add new edges for this block
            if let Some(block_data) = new_blocks_map.get(&block) {
                let (_, _, successful_txs) = block_data;

                if !successful_txs.is_empty() {
                    let mut block_edges = Vec::new();
                    for &(token, from, to, amount) in successful_txs.iter() {
                        let (from_idx, _) = self.get_or_add_node(from);
                        let (to_idx, _) = self.get_or_add_node(to);

                        // Remove from orphan candidates - these nodes are active again
                        total_orphan_candidates.remove(&from_idx);
                        total_orphan_candidates.remove(&to_idx);

                        let eidx = self.graph.add_edge(
                            from_idx,
                            to_idx,
                            TransferEdge { amount, block }
                        );
                        block_edges.push(eidx);
                    }
                    self.per_block_edges.insert(block, block_edges);
                }
            }
            // Block stays in queue - no queue changes needed
        }

        // Phase 2: Handle blocks ONLY in old (delete)
        for &block in blocks_only_in_old {
            if let Some(edge_idxs) = self.per_block_edges.remove(&block) {
                for eidx in edge_idxs {
                    if let Some((source, target)) = self.graph.edge_endpoints(eidx) {
                        total_orphan_candidates.insert(source);
                        total_orphan_candidates.insert(target);
                    }
                    self.graph.remove_edge(eidx);
                }
            }
        }

        // Phase 3: Handle blocks ONLY in new (add)
        for &block in blocks_only_in_new {
            if let Some(block_data) = new_blocks_map.get(&block) {
                let (_, _, successful_txs) = block_data;

                if !successful_txs.is_empty() {
                    let mut block_edges = Vec::new();
                    for &(token, from, to, amount) in successful_txs.iter() {
                        let (from_idx, _) = self.get_or_add_node(from);
                        let (to_idx, _) = self.get_or_add_node(to);

                        // Remove from orphan candidates
                        total_orphan_candidates.remove(&from_idx);
                        total_orphan_candidates.remove(&to_idx);

                        let eidx = self.graph.add_edge(
                            from_idx,
                            to_idx,
                            TransferEdge { amount, block }
                        );
                        block_edges.push(eidx);
                    }
                    self.per_block_edges.insert(block, block_edges);
                }
            }
        }

        // Phase 4: Fix block queue (remove old, add new, keep sorted)
        // Start with current queue minus blocks only in old
        let mut final_blocks: Vec<u64> = self.block_queue
            .iter()
            .copied()
            .filter(|b| !blocks_only_in_old.contains(b))
            .collect();

        // Add blocks only in new
        final_blocks.extend_from_slice(blocks_only_in_new);

        // Sort and deduplicate
        final_blocks.sort_unstable();
        final_blocks.dedup();

        // Replace queue
        self.block_queue.clear();
        self.block_queue.extend(final_blocks);

        // Phase 5: Clean up orphaned nodes (single pass at the end)
        if !total_orphan_candidates.is_empty() {
            let removed = self.orphan_node_removal(total_orphan_candidates);
            println!("Reorg: removed {} orphaned nodes", removed);
        }

        // Clear any building state
        self.overlay.clear();
        self.building_block = None;

        println!(
            "Reorg complete: {} nodes, {} edges across {} blocks",
            self.graph.node_count(),
            self.graph.edge_count(),
            self.block_queue.len()
        );
    }

    // ------------------------------------------
    // ROLLING PRUNE
    // ------------------------------------------
    /// Prunes edges outside the block window and removes orphaned nodes
    fn prune(&mut self, current_block: u64) {
        // TODO: Remove these initial counts
        let nodes_before = self.graph.node_count();
        let edges_before = self.graph.edge_count();

        let mut blocks_to_prune = Vec::new();
        let mut edges_to_remove = Vec::new();
        let mut orphan_candidates = FxHashSet::default();

        while let Some(&old) = self.block_queue.front() {
            if current_block - old < self.config.window_blocks {
                break;
            }
            blocks_to_prune.push(old);
            self.block_queue.pop_front();

            if let Some(edges) = self.per_block_edges.get(&old) {
                for &eidx in edges {
                    // Collect endpoints before removing edge
                    if let Some((source, target)) = self.graph.edge_endpoints(eidx) {
                        orphan_candidates.insert(source);
                        orphan_candidates.insert(target);
                    }
                }
                edges_to_remove.extend(edges.iter().copied());
            }
        }

        for eidx in edges_to_remove {
            self.graph.remove_edge(eidx);
        }

        for blk in blocks_to_prune {
            self.per_block_edges.remove(&blk);
        }

        if !orphan_candidates.is_empty() {
            self.orphan_node_removal(orphan_candidates);
        }

        // println!(
        //     "Prune complete: nodes {} -> {}, edges {} -> {}",
        //     nodes_before, self.graph.node_count(),
        //     edges_before, self.graph.edge_count()
        // );
    }

    /// Removes nodes that have no incoming or outgoing edges.
    /// Returns the number of nodes removed.
    fn orphan_node_removal(&mut self, candidates: FxHashSet<NodeIndex>) -> usize {
        let mut removed_count = 0;

        for node in candidates {
            // Check if node has any edges at all (single traversal)
            if self.graph.neighbors_directed(node, Incoming).next().is_none()
                && self.graph.neighbors_directed(node, Outgoing).next().is_none(){
                // Remove from node_map
                if let Some(node_addr) = self.graph.node_weight(node) {
                    self.node_map.remove(node_addr);
                }
                // Remove from graph
                self.graph.remove_node(node);
                removed_count += 1;
            }
        }

        removed_count
    }

    pub fn estimate_internal_memory(&self) -> usize {
        let mut total = 0usize;

        // 1. node_map: HashMap<Address, NodeIndex>
        total += self.node_map.capacity() * (std::mem::size_of::<Address>() + std::mem::size_of::<NodeIndex>());

        // 2. graph nodes and edges using capacity
        let (node_capacity, edge_capacity) = self.graph.capacity();
        total += node_capacity * (std::mem::size_of::<Address>() + 2 * std::mem::size_of::<usize>());
        total += edge_capacity * (std::mem::size_of::<TransferEdge>() + 4 * std::mem::size_of::<usize>());

        // 3. overlay outgoing_pairs: HashMap capacity + all Vec capacities
        total += self.overlay.outgoing_pairs.capacity() * std::mem::size_of::<Address>();
        for vec in self.overlay.outgoing_pairs.values() {
            total += vec.capacity() * std::mem::size_of::<(Address, TransferEdge)>();
        }

        // 4. overlay incoming_pairs: HashMap capacity + all Vec capacities
        total += self.overlay.incoming_pairs.capacity() * std::mem::size_of::<Address>();
        for vec in self.overlay.incoming_pairs.values() {
            total += vec.capacity() * std::mem::size_of::<(Address, TransferEdge)>();
        }
        total += self.overlay.pair_sum.capacity() * (
            std::mem::size_of::<(Address, Address)>() +  // key: (from, to)
                std::mem::size_of::<(U256, u64)>() +          // value: (sum, max_block)
                std::mem::size_of::<usize>()                  // hash bucket overhead
        );

        // 5. per_block_edges: HashMap + Vecs
        total += self.per_block_edges.capacity() * std::mem::size_of::<u64>();
        for vec in self.per_block_edges.values() {
            total += vec.capacity() * std::mem::size_of::<EdgeIndex>();
        }

        // 6. block_queue
        total += self.block_queue.capacity() * std::mem::size_of::<u64>();

        // 8. block_caches.base_pair_sum: (Address, Address) -> (U256, u64)
        total += self.block_caches.base_pair_sum.capacity() * (
            std::mem::size_of::<(Address, Address)>() +   // key: 40 bytes
                std::mem::size_of::<(U256, u64)>() +          // value: 40 bytes
                std::mem::size_of::<usize>()                  // hash bucket overhead: 8 bytes
        );

        // 9. block_caches.neighbors_in: Address -> FxHashSet<Address>
        total += self.block_caches.neighbors_in.capacity() * (
            std::mem::size_of::<Address>() +              // key: 20 bytes
                std::mem::size_of::<usize>() * 3              // HashSet overhead (ptr, cap, len): 24 bytes
        );
        for neighbor_set in self.block_caches.neighbors_in.values() {
            total += neighbor_set.capacity() * (
                std::mem::size_of::<Address>() +          // Address: 20 bytes
                    std::mem::size_of::<usize>()              // hash bucket: 8 bytes
            );
        }

        // 10. block_caches.neighbors_out: Address -> FxHashSet<Address>
        total += self.block_caches.neighbors_out.capacity() * (
            std::mem::size_of::<Address>() +              // key: 20 bytes
                std::mem::size_of::<usize>() * 3              // HashSet overhead: 24 bytes
        );
        for neighbor_set in self.block_caches.neighbors_out.values() {
            total += neighbor_set.capacity() * (
                std::mem::size_of::<Address>() +          // Address: 20 bytes
                    std::mem::size_of::<usize>()              // hash bucket: 8 bytes
            );
        }

        total
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
        assert!(d.consensus_validate_block(&txs, block, parent_hash(block-1)).len() > 0);
        // All temp edges rolled back
        assert_eq!(d.graph.edge_count(), 0);
        assert!(d.building_block.is_none());
    }

    // --------------------------------
    // 4) Pruning: edges removed when outside window
    // --------------------------------
    #[test]
    fn pruning_removes_old_edges() {
        let mut d = AMLMotifDetector::new(cfg());
        let a = addr("0x6000000000000000000000000000000000000001");
        let b = addr("0x6000000000000000000000000000000000000002");

        // Commit blocks 0..=6 (window_blocks=5 -> keeps blocks 1..=5 at current_block=6)
        for blk in 0..=6 {
            let txs = vec![(ZERO_ADDRESS, a, b, U256::from(1))];
            let parent = parent_hash(0);
            assert!(d.consensus_validate_block(&txs, blk, parent).len() == 0);
            d.block_commit(blk, parent, &txs);
        }
        // Inclusive boundary: blocks 1..=5 remain -> 5 edges
        assert_eq!(d.graph.edge_count(), 5);
    }

    // -----------------------------
    // 1) Proposer: evaluate-then-append (no rollback)
    // -----------------------------
    #[test]
    fn proposer_fan_out_evaluate_then_append() {
        let mut d = AMLMotifDetector::new(cfg());
        let src = addr("0x2000000000000000000000000000000000000001");
        let r1  = addr("0x2000000000000000000000000000000000000002");
        let r2  = addr("0x2000000000000000000000000000000000000003");

        // Start building block 10
        let block = 10;
        let phash = parent_hash(block - 1);

        // First tx (clean) -> appended to overlay
        let suspicious_1 = d.proposer_check_tx(src, r1, U256::from(6), ZERO_ADDRESS, block, phash);
        assert!(!suspicious_1, "first tx should be clean and appended");

        // Second tx with amount 6 would tip fan-out SUM to 12 (>10) -> suspicious (NOT appended)
        let suspicious_2 = d.proposer_check_tx(src, r2, U256::from(6), ZERO_ADDRESS, block, phash);
        assert!(suspicious_2, "second tx should be suspicious due to fan-out sum 12 > 10");

        // A reduced second tx (amount 4) should now be accepted (sum 10 == threshold; count=2 <= 3)
        let suspicious_2b = d.proposer_check_tx(src, r2, U256::from(4), ZERO_ADDRESS, block, phash);
        assert!(!suspicious_2b, "second tx (4) should be clean and appended");
    }

    // -----------------------------
    // 2) Consensus: incremental detection; base graph untouched
    // -----------------------------
    #[test]
    fn consensus_fan_out_illicit_indices_and_no_commit() {
        let mut d = AMLMotifDetector::new(cfg());
        let src = addr("0x2100000000000000000000000000000000000001");
        let r1  = addr("0x2100000000000000000000000000000000000002");
        let r2  = addr("0x2100000000000000000000000000000000000003");

        let block = 20;
        let phash = parent_hash(block - 1);

        // t1 clean (6), t2 would tip to 12 -> illicit index = 1
        let txs = vec![(ZERO_ADDRESS, src, r1, U256::from(6)),
                       (ZERO_ADDRESS, src, r2, U256::from(6))];

        let illicit = d.consensus_validate_block(&txs, block, phash);
        assert_eq!(illicit, vec![1], "second tx must be flagged illicit");

        // Base graph is untouched until commit
        assert_eq!(d.graph.edge_count(), 0, "no edges committed by consensus validation");
    }

    // -----------------------------
    // 3) Fan-In motif (receiver-centric)
    // -----------------------------
    #[test]
    fn motifs_fan_in_receiver_thresholds() {
        let mut d = AMLMotifDetector::new(cfg());
        let a1 = addr("0x1000000000000000000000000000000000000001");
        let a2 = addr("0x1000000000000000000000000000000000000002");
        let a3 = addr("0x1000000000000000000000000000000000000003");
        let sink = addr("0x10000000000000000000000000000000000000ff");
        let block = 30;
        let phash = parent_hash(block - 1);

        // Two contributions of 5 -> sum 10 == threshold; not suspicious yet
        assert!(!d.proposer_check_tx(a1, sink, U256::from(5), ZERO_ADDRESS, block, phash));
        assert!(!d.proposer_check_tx(a2, sink, U256::from(5), ZERO_ADDRESS, block, phash));

        // Third small contribution tips sum to 11 -> suspicious
        let suspicious_3 = d.proposer_check_tx(a3, sink, U256::from(1), ZERO_ADDRESS, block, phash);
        assert!(suspicious_3, "third tx should be suspicious due to fan-in sum 11 > 10");
    }

    // -----------------------------
    // 4) Scatter-Gather motif (source -> intermediaries -> sink)
    // -----------------------------
    #[test]
    fn motifs_scatter_gather_threshold() {
        let mut d = AMLMotifDetector::new(cfg());
        let source = addr("0x3000000000000000000000000000000000000001");
        let i1     = addr("0x3000000000000000000000000000000000000002");
        let i2     = addr("0x3000000000000000000000000000000000000003");
        let sink   = addr("0x30000000000000000000000000000000000000aa");
        let block  = 40;
        let phash  = parent_hash(block - 1);

        // Build the paths incrementally using proposer (overlay-only)
        assert!(!d.proposer_check_tx(source, i1, U256::from(5), ZERO_ADDRESS, block, phash));
        assert!(!d.proposer_check_tx(i1, sink,   U256::from(5), ZERO_ADDRESS, block, phash));
        assert!(!d.proposer_check_tx(source, i2, U256::from(5), ZERO_ADDRESS, block, phash));

        // Final hop i2->sink creates two intermediaries converging -> bottleneck total 10 > 8 -> suspicious
        let suspicious_final = d.proposer_check_tx(i2, sink, U256::from(5), ZERO_ADDRESS, block, phash);
        assert!(suspicious_final, "scatter-gather pattern should be flagged");
    }

    // -----------------------------
    // 5) Gather-Scatter motif (hub behavior)
    // -----------------------------
    #[test]
    fn motifs_gather_scatter_hub() {
        let mut d = AMLMotifDetector::new(cfg());
        let s1   = addr("0x4000000000000000000000000000000000000001");
        let s2   = addr("0x4000000000000000000000000000000000000002");
        let hub  = addr("0x40000000000000000000000000000000000000bb");
        let recv = addr("0x40000000000000000000000000000000000000bc");
        let block = 50;
        let phash = parent_hash(block - 1);

        assert!(!d.proposer_check_tx(s1, hub, U256::from(5), ZERO_ADDRESS, block, phash));
        assert!(!d.proposer_check_tx(s2, hub, U256::from(5), ZERO_ADDRESS, block, phash));

        // Hub -> receiver with 10 should trip gather-scatter (two sources feed the hub)
        let suspicious = d.proposer_check_tx(hub, recv, U256::from(10), ZERO_ADDRESS, block, phash);
        assert!(suspicious, "gather-scatter (hub) must be flagged");
    }

    // -----------------------------
    // 6) Consensus uses same logic for self-built blocks (no clearing)
    // -----------------------------
    #[test]
    fn consensus_ignores_proposer_overlay_for_same_block() {
        let mut d = AMLMotifDetector::new(cfg());
        let block = 60;
        let phash = parent_hash(block - 1);

        let src = addr("0x6000000000000000000000000000000000000001");
        let r1  = addr("0x6000000000000000000000000000000000000002");
        let r2  = addr("0x6000000000000000000000000000000000000003");

        // Proposer builds overlay context (but consensus will start clean)
        assert!(!d.proposer_check_tx(src, r1, U256::from(6), ZERO_ADDRESS, block, phash));

        // Consensus validates SAME block with a second tx; overlay is cleared at start
        let txs = vec![(ZERO_ADDRESS, src, r2, U256::from(6))];
        let illicit = d.consensus_validate_block(&txs, block, phash);

        // No prior context visible -> not flagged
        assert!(illicit.is_empty(), "consensus starts clean; should not see proposer overlay");
        assert_eq!(d.graph.edge_count(), 0, "no commit during validation");
    }

    // -----------------------------
    // 7) Commit updates base graph only at block_commit
    // -----------------------------
    #[test]
    fn commit_only_updates_base_graph() {
        let mut d = AMLMotifDetector::new(cfg());
        let block = 70;
        let phash = parent_hash(block - 1);

        let a = addr("0x7000000000000000000000000000000000000001");
        let b = addr("0x7000000000000000000000000000000000000002");

        // Validate a clean single-tx block (no commits yet)
        let txs = vec![(ZERO_ADDRESS, a, b, U256::from(1))];
        let illicit = d.consensus_validate_block(&txs, block, phash);
        assert!(illicit.is_empty(), "tx should be clean in consensus");

        assert_eq!(d.graph.edge_count(), 0, "no commit during validation");

        // Commit the block
        d.block_commit(block, phash, &txs);

        assert_eq!(d.graph.edge_count(), 1, "edge must be committed at block_commit");
    }

    // -----------------------------
    // 8) Fan-In window respects committed history
    // -----------------------------
    #[test]
    fn fan_in_counts_include_committed_within_window() {
        let mut d = AMLMotifDetector::new(cfg());
        let sink = addr("0x80000000000000000000000000000000000000ff");
        let s1   = addr("0x8000000000000000000000000000000000000001");
        let s2   = addr("0x8000000000000000000000000000000000000002");
        let s3   = addr("0x8000000000000000000000000000000000000003");

        // Commit two prior blocks with sender->sink edges inside window
        for blk in 90..=91 {
            let txs = vec![(ZERO_ADDRESS, if blk == 90 { s1 } else { s2 }, sink, U256::from(5))];
            assert!(d.consensus_validate_block(&txs, blk, parent_hash(blk - 1)).is_empty());
            d.block_commit(blk, parent_hash(blk - 1), &txs);
        }
        assert_eq!(d.graph.edge_count(), 2);

        // At current block 92 (within window_blocks=5), adding s3->sink(1) should tip fan-in sum 11 > 10
        let current = 92;
        let phash   = parent_hash(current - 1);
        let suspicious = d.proposer_check_tx(s3, sink, U256::from(1), ZERO_ADDRESS, current, phash);
        assert!(suspicious, "fan-in with committed history should be considered in motif checks");
    }


    #[test]
    fn consensus_detects_fan_in_pattern() {
        let mut d = AMLMotifDetector::new(cfg());
        let sink = addr("0x10000000000000000000000000000000000000ff");
        let s1 = addr("0x1000000000000000000000000000000000000001");
        let s2 = addr("0x1000000000000000000000000000000000000002");
        let s3 = addr("0x1000000000000000000000000000000000000003");

        let block = 10;
        let phash = parent_hash(block - 1);

        // Three senders → sink; sum > threshold
        let txs = vec![
            (ZERO_ADDRESS, s1, sink, U256::from(5)),
            (ZERO_ADDRESS, s2, sink, U256::from(5)),
            (ZERO_ADDRESS, s3, sink, U256::from(1)),
        ];

        let illicit = d.consensus_validate_block(&txs, block, phash);
        assert_eq!(illicit, vec![2], "third tx should trigger fan-in detection");
    }


    #[test]
    fn consensus_detects_fan_out_pattern() {
        let mut d = AMLMotifDetector::new(cfg());
        let src = addr("0x2000000000000000000000000000000000000001");
        let r1 = addr("0x2000000000000000000000000000000000000002");
        let r2 = addr("0x2000000000000000000000000000000000000003");

        let block = 20;
        let phash = parent_hash(block - 1);

        let txs = vec![
            (ZERO_ADDRESS, src, r1, U256::from(6)),
            (ZERO_ADDRESS, src, r2, U256::from(6)), // triggers fan-out sum > threshold
        ];

        let illicit = d.consensus_validate_block(&txs, block, phash);
        assert_eq!(illicit, vec![1], "second tx should trigger fan-out detection");
    }


    #[test]
    fn consensus_detects_scatter_gather_pattern() {
        let mut d = AMLMotifDetector::new(cfg());
        let source = addr("0x3000000000000000000000000000000000000001");
        let i1 = addr("0x3000000000000000000000000000000000000002");
        let i2 = addr("0x3000000000000000000000000000000000000003");
        let sink = addr("0x30000000000000000000000000000000000000aa");

        let block = 30;
        let phash = parent_hash(block - 1);

        let txs = vec![
            (ZERO_ADDRESS, source, i1, U256::from(5)),
            (ZERO_ADDRESS, i1, sink, U256::from(5)),
            (ZERO_ADDRESS, source, i2, U256::from(5)),
            (ZERO_ADDRESS, i2, sink, U256::from(5)), // triggers scatter-gather
        ];

        let illicit = d.consensus_validate_block(&txs, block, phash);
        assert_eq!(illicit, vec![3], "fourth tx should trigger scatter-gather detection");
    }


    #[test]
    fn consensus_detects_gather_scatter_pattern() {
        let mut d = AMLMotifDetector::new(cfg());
        let s1 = addr("0x4000000000000000000000000000000000000001");
        let s2 = addr("0x4000000000000000000000000000000000000002");
        let hub = addr("0x40000000000000000000000000000000000000bb");
        let recv = addr("0x40000000000000000000000000000000000000bc");

        let block = 40;
        let phash = parent_hash(block - 1);

        let txs = vec![
            (ZERO_ADDRESS, s1, hub, U256::from(5)),
            (ZERO_ADDRESS, s2, hub, U256::from(5)),
            (ZERO_ADDRESS, hub, recv, U256::from(10)), // triggers gather-scatter
        ];

        let illicit = d.consensus_validate_block(&txs, block, phash);
        assert_eq!(illicit, vec![2], "third tx should trigger gather-scatter detection");
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
