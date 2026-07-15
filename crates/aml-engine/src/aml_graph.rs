use std::io::Write;
use petgraph::stable_graph::{StableGraph, NodeIndex, EdgeIndex};
use petgraph::Direction::{Incoming, Outgoing};
use std::collections::{HashMap, VecDeque};
use std::fs;
use std::fs::OpenOptions;
use std::sync::Mutex;
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use alloy_primitives::{Address, B256, U256};
use chrono::Local;
use lazy_static::lazy_static;
use rustc_hash::{FxHashMap, FxHashSet};
use rayon::prelude::*;

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
    pub scatter_gather_count_threshold: u64,
    /// Gather-scatter: threshold for total flow to sink through multiple destinations
    pub gather_scatter_threshold: U256,
    pub gather_scatter_count_threshold: u64,
    pub fan_out_count_threshold: u64,
    pub fan_out_sum_threshold: U256,
}

#[derive(Clone, Debug)]
pub struct TransferEdge {
    pub amount: U256,
    pub block: u64,
}

#[derive(Default, Clone)]
pub struct MotifResult {
    pub fan_out: bool,
    pub gather_scatter: bool,
    pub fan_in: bool,
    pub scatter_gather: bool,
}

impl MotifResult {
    pub fn is_suspicious(&self) -> bool {
        self.fan_out || self.gather_scatter || self.fan_in || self.scatter_gather
    }
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

#[derive(Default)]
struct MotifCounts {
    fan_in: u64,
    fan_out: u64,
    scatter_gather: u64,
    gather_scatter: u64,
}

lazy_static! {
    static ref RUN_TIMESTAMP: String = {
        let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
        let path = format!("experiment_logs_patterns/{}", timestamp);
        fs::create_dir_all(&path).expect("Failed to create run directory");
        timestamp
    };

    static ref PATTERNS_LOG: Mutex<std::fs::File> = Mutex::new({
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("experiment_logs_patterns/{}/patterns.csv", *RUN_TIMESTAMP))
            .expect("Failed to open patterns.csv");
        writeln!(file, "unix_timestamp,block_number,fan_in,fan_out,scatter_gather,gather_scatter")
            .expect("Failed to write header");
        file
    });

    static ref BUCKET_LOG: Mutex<std::fs::File> = Mutex::new({
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("experiment_logs_patterns/{}/bucket.csv", *RUN_TIMESTAMP))
            .expect("Failed to open bucket.csv");
        writeln!(file, "unix_timestamp,block_number,number_of_buckets,partition_time")
            .expect("Failed to write header");
        file
    });

}

fn get_unix_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

pub fn log_pattern_counts(block_number: u64, counts: &MotifCounts) {
    if let Ok(mut file) = PATTERNS_LOG.lock() {
        writeln!(
            file,
            "{},{},{},{},{},{}",
            get_unix_timestamp(),
            block_number,
            counts.fan_in,
            counts.fan_out,
            counts.scatter_gather,
            counts.gather_scatter,
        ).ok();
    }
}

pub fn log_bucket_count(
    block_number: u64,
    num_buckets: usize,
    latency_micros: u128,
) {
    if let Ok(mut file) = BUCKET_LOG.lock() {
        writeln!(
            file,
            "{},{},{},{}",
            get_unix_timestamp(),
            block_number,
            num_buckets,
            latency_micros
        ).ok();
    }
}

// ---------------------------------------------------------------------------
// Union-Find for dependency buckets
// ---------------------------------------------------------------------------

struct UnionFind {
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            size: vec![1; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        let p = self.parent[x];

        if p != x {
            let r = self.find(p);
            self.parent[x] = r;
        }

        self.parent[x]
    }

    fn union(&mut self, a: usize, b: usize) {
        let mut ra = self.find(a);
        let mut rb = self.find(b);

        if ra == rb {
            return;
        }

        if self.size[ra] < self.size[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }

        self.parent[rb] = ra;
        self.size[ra] += self.size[rb];
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
        if out.capacity() < cached.len() {
            out.reserve(cached.len().saturating_sub(out.capacity()));
        }
        out.extend(cached.iter().copied());

        if let Some((efrom, eto, _)) = ephemeral {
            match dir {
                Incoming if eto == addr => {
                    if !cached.contains(&efrom) {
                        out.push(efrom);
                    }
                }
                Outgoing if efrom == addr => {
                    if !cached.contains(&eto) {
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
    ) -> MotifResult  {
        let mut result = MotifResult::default();

        let mut incoming = Vec::new();
        self.neighbors_to_vec_with_ephemeral(to_addr, Incoming, ephemeral, &mut incoming);

        // 1) FAN-IN
        let mut fan_in_count = 0u64;
        let mut fan_in_sum = U256::ZERO;
        for &src_addr in &incoming {
            let (neighbor_total, _maxb) =
                self.window_sum_full(src_addr, to_addr, current_block, ephemeral);
            if neighbor_total > U256::ZERO {
                fan_in_count += 1;
                fan_in_sum += neighbor_total;
                if fan_in_count > self.config.fan_in_count_threshold
                    || fan_in_sum > self.config.fan_in_sum_threshold
                {
                    // println!("fan in detected");
                    result.fan_in = true;
                    return result;
                }
            }
        }

        // 2) SCATTER-GATHER
        // Each intermediary is visited once, and each src list comes from a cached set,
        // so a per-source intermediary count is enough; no nested FxHashSet is needed.
        let mut source_data: FxHashMap<Address, (u64, U256)> = FxHashMap::default();
        for &inter_addr in &incoming {
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
                        .or_insert((0, U256::ZERO));
                    entry.0 += 1;
                    entry.1 += bottleneck;
                }
            }
        }
        for (_src, (inter_count, total_flow)) in source_data.into_iter() {
            if inter_count > self.config.scatter_gather_count_threshold && total_flow > self.config.scatter_gather_threshold {
                // println!("scatter gather detected");
                result.scatter_gather = true;
                return result;
            }
        }

        result
    }

    /// Sender-centric motifs: fan-out & gather-scatter (hub behavior)
    fn check_motifs_from_view_ephemeral(
        &mut self,
        from_addr: Address,
        current_block: u64,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
    ) -> MotifResult  {
        let mut result = MotifResult::default();

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
                    result.fan_out = true;
                    return result;
                }
            }
        }

        // 2) GATHER-SCATTER (hub): multiple sources → from_addr → one receiver
        let mut sources = Vec::new();
        self.neighbors_to_vec_with_ephemeral(from_addr, Incoming, ephemeral, &mut sources);

        let sources_len = sources.len();
        let mut incoming_sum = U256::ZERO;
        for src_addr in sources.into_iter() {
            let (sum, _maxb) = self.window_sum_full(src_addr, from_addr, current_block, ephemeral);
            incoming_sum += sum;
        }

        let flow_volume = incoming_sum.min(fan_out_sum);
        if sources_len as u64 > self.config.gather_scatter_count_threshold
            && fan_out_count > self.config.gather_scatter_count_threshold
            && flow_volume > self.config.gather_scatter_threshold
        {
            result.gather_scatter = true;
            return result;
        }

        result
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
    ) -> (MotifResult, MotifResult) {
        let edge = TransferEdge { amount, block };
        let ephemeral = Some((from, to, &edge));
        let suspicious_from = self.check_motifs_from_view_ephemeral(from, block, ephemeral);
        if suspicious_from.is_suspicious() {
            return (suspicious_from, MotifResult::default());
        }
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

        let (from_result, to_result) = self.would_be_suspicious(token, from, to, amount, block);

        log_pattern_counts(block, &MotifCounts {
            fan_out: from_result.fan_out as u64,
            gather_scatter: from_result.gather_scatter as u64,
            fan_in: to_result.fan_in as u64,
            scatter_gather: to_result.scatter_gather as u64,
        });

        if from_result.is_suspicious() || to_result.is_suspicious() {
            true
        } else {
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
            if suspicious_from.is_suspicious() || suspicious_to.is_suspicious() {
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
        // let nodes_before = self.graph.node_count();
        // let edges_before = self.graph.edge_count();

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

    // ----------------------------------------------------------------------------
    // Dependency bucketing for parallel validator-side validation
    // ----------------------------------------------------------------------------

    /// Groups transaction indices into independent buckets.
    ///
    /// Correctness invariant:
    /// If tx_i can affect the AML verdict of tx_j under the original sequential
    /// algorithm, then tx_i and tx_j must be placed in the same bucket.
    ///
    /// False positives are safe: they only create larger buckets and reduce
    /// parallelism. False negatives are unsafe: they can make the parallel result
    /// differ from the sequential baseline.
    ///
    /// This assumes every validator has the same full graph. We are splitting
    /// work, not graph state.
    fn partition_into_buckets(
        &self,
        txs: &[(Address, Address, Address, U256)],
    ) -> Vec<Vec<usize>> {
        let n = txs.len();

        if n == 0 {
            return Vec::new();
        }

        let mut uf = UnionFind::new(n);
        let mut owner: FxHashMap<Address, usize> = FxHashMap::default();

        // Cache historical SG intermediaries per receiver:
        // sg_intermediary_cache[to] = { inter | historical edge inter -> to exists }.
        let mut sg_intermediary_cache: FxHashMap<Address, Vec<Address>> = FxHashMap::default();

        // Tracks addresses that appeared as receivers in earlier candidate txs.
        //
        // This makes the in-block SG case explicit:
        //
        //      previous candidate: src -> inter
        //      historical graph:   inter -> to
        //      current candidate:  x -> to
        //
        // The previous candidate may create new flow into an SG intermediary for
        // the current receiver `to`, so it must be in the same bucket.
        let mut in_block_receiver_owner: FxHashMap<Address, usize> = FxHashMap::default();

        fn touch(
            uf: &mut UnionFind,
            owner: &mut FxHashMap<Address, usize>,
            addr: Address,
            idx: usize,
        ) {
            match owner.entry(addr) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    uf.union(*e.get(), idx);
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(idx);
                }
            }
        }

        for (idx, &(_token, from, to, _amount)) in txs.iter().enumerate() {
            // Direct dependencies.
            //
            // This captures:
            // - same sender fan-out interactions
            // - same receiver fan-in interactions
            // - gather-scatter hub interactions
            // - same-block two-hop chains sharing the intermediary directly
            touch(&mut uf, &mut owner, from, idx);
            touch(&mut uf, &mut owner, to, idx);

            // Scatter-Gather dependency expansion.
            //
            // When evaluating SG for receiver `to`, the algorithm scans existing
            // intermediaries `inter` with historical edges:
            //
            //      inter -> to
            //
            // and then checks incoming edges into each `inter`.
            //
            // Therefore, any candidate transaction touching such an intermediary
            // can affect this tx's SG verdict and must be bucketed together.
            let inters = sg_intermediary_cache.entry(to).or_insert_with(|| {
                let mut v = Vec::new();

                if let Some(&to_idx) = self.node_map.get(&to) {
                    for nbr in self.graph.neighbors_directed(to_idx, Incoming) {
                        if let Some(&inter) = self.graph.node_weight(nbr) {
                            v.push(inter);
                        }
                    }
                }

                v
            });

            for &inter in inters.iter() {
                // If any earlier/future tx touches this historical intermediary,
                // it must be in the same bucket.
                touch(&mut uf, &mut owner, inter, idx);

                // Explicit in-block receiver case:
                // if a prior tx had receiver == inter, then it may add new flow
                // into an SG intermediary relevant for current receiver `to`.
                //
                // In many cases this is already covered by touch(inter, idx),
                // because prior receivers are also touched addresses. Keeping
                // this explicit is harmless and documents the intended dependency.
                if let Some(&prev_idx) = in_block_receiver_owner.get(&inter) {
                    uf.union(prev_idx, idx);
                }
            }

            // Mark this tx's receiver for later SG dependency expansion.
            //
            // If multiple txs share this receiver, direct touch(to, idx) already
            // unions them, so keeping the first owner is sufficient.
            in_block_receiver_owner.entry(to).or_insert(idx);
        }

        let mut groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();

        for idx in 0..n {
            let root = uf.find(idx);
            groups.entry(root).or_default().push(idx);
        }

        let mut buckets: Vec<Vec<usize>> = groups.into_values().collect();

        // Preserve original block order inside each bucket.
        for bucket in buckets.iter_mut() {
            bucket.sort_unstable();
        }

        // Deterministic bucket order. Not required for correctness, useful for
        // reproducibility and debugging.
        buckets.sort_by_key(|bucket| bucket[0]);

        buckets
    }

    /// Parallel validator-side AML validation using dependency buckets.
    ///
    /// This function does not mutate the global graph. It returns tx indices
    /// that should be rejected. The caller should commit accepted txs later in
    /// original block order.
    ///
    /// Semantics:
    /// - All validators still have the same full graph.
    /// - All validators still validate the full proposed block.
    /// - This only parallelizes independent buckets locally.
    /// - Transactions inside each bucket are processed sequentially.
    pub fn consensus_validate_block_parallel_buckets(
        &self,
        txs: &[(Address, Address, Address, U256)],
        block: u64,
        _parent_hash: B256,
    ) -> Vec<usize> {
        if txs.is_empty() {
            return Vec::new();
        }

        let start = Instant::now();
        let buckets = self.partition_into_buckets(txs);
        let elapsed = start.elapsed().as_micros();
        log_bucket_count(block, buckets.len(), elapsed);

        let graph = &self.graph;
        let node_map = &self.node_map;
        let config = &self.config;

        let mut illicit_indices: Vec<usize> = buckets
            .par_iter()
            .flat_map_iter(|bucket| {
                let mut overlay = BlockOverlay::default();
                let mut caches = BlockCaches::default();
                let mut local_illicit = Vec::new();

                // Sequential within bucket because txs in the same bucket may
                // have prefix dependencies.
                for &idx in bucket {
                    let (_token, from, to, amount) = txs[idx];

                    let (suspicious_from, suspicious_to) = would_be_suspicious_bucket(
                        graph,
                        node_map,
                        &mut overlay,
                        &mut caches,
                        config,
                        from,
                        to,
                        amount,
                        block,
                    );

                    if suspicious_from.is_suspicious() || suspicious_to.is_suspicious() {
                        local_illicit.push(idx);
                    } else {
                        overlay.append(from, to, TransferEdge { amount, block });
                        update_neighbor_cache_for_edge_bucket(&mut caches, from, to);
                    }
                }

                local_illicit
            })
            .collect();

        illicit_indices.sort_unstable();
        illicit_indices.dedup();

        illicit_indices
    }

    /// Helper: derive accepted tx indices from rejected tx indices.
    ///
    /// Commit accepted txs using original block order. Do not merge bucket
    /// overlays into the global graph; bucket overlays are local execution
    /// artifacts only.
    pub fn accepted_indices_from_illicit(
        tx_count: usize,
        illicit_indices: &[usize],
    ) -> Vec<usize> {
        let illicit: FxHashSet<usize> = illicit_indices.iter().copied().collect();

        (0..tx_count)
            .filter(|idx| !illicit.contains(idx))
            .collect()
    }

}

// ============================================================================
// Bucket-local helper functions
//
// Bucket-local means:
//     shared immutable committed graph
//   + bucket-local overlay of accepted txs
//   + bucket-local caches
//   + ephemeral current tx being tested
//
// It does NOT mean a different graph truth.
// ============================================================================

fn base_pair_sum_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    caches: &mut BlockCaches,
    config: &Config,
    a: Address,
    b: Address,
    current_block: u64,
) -> (U256, u64) {
    if let Some(v) = caches.base_pair_sum.get(&(a, b)) {
        return *v;
    }

    let mut sum = U256::ZERO;
    let mut maxb = 0u64;

    if let (Some(&ai), Some(&bi)) = (node_map.get(&a), node_map.get(&b)) {
        for e in graph.edges_connecting(ai, bi) {
            let w = e.weight();

            if current_block >= w.block && current_block - w.block < config.window_blocks {
                sum += w.amount;
                maxb = maxb.max(w.block);
            }
        }
    }

    let v = (sum, maxb);
    caches.base_pair_sum.insert((a, b), v);
    v
}

fn window_sum_full_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    overlay: &BlockOverlay,
    caches: &mut BlockCaches,
    config: &Config,
    a: Address,
    b: Address,
    current_block: u64,
    ephemeral: Option<(Address, Address, &TransferEdge)>,
) -> (U256, u64) {
    let (mut sum, mut maxb) =
        base_pair_sum_bucket(graph, node_map, caches, config, a, b, current_block);

    let (osum, omax) = overlay.overlay_pair(a, b);

    if omax != 0 && current_block >= omax && current_block - omax < config.window_blocks {
        sum += osum;
        maxb = maxb.max(omax);
    }

    if let Some((ea, eb, ew)) = ephemeral {
        if ea == a
            && eb == b
            && current_block >= ew.block
            && current_block - ew.block < config.window_blocks
        {
            sum += ew.amount;
            maxb = maxb.max(ew.block);
        }
    }

    (sum, maxb)
}

fn ensure_neighbors_cached_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    overlay: &BlockOverlay,
    caches: &mut BlockCaches,
    addr: Address,
    dir: petgraph::Direction,
) {
    let map = match dir {
        Incoming => &mut caches.neighbors_in,
        Outgoing => &mut caches.neighbors_out,
    };

    if map.contains_key(&addr) {
        return;
    }

    let mut set = FxHashSet::default();

    if let Some(&nidx) = node_map.get(&addr) {
        for n in graph.neighbors_directed(nidx, dir) {
            if let Some(&a) = graph.node_weight(n) {
                set.insert(a);
            }
        }
    }

    match dir {
        Outgoing => {
            for (to, _e) in overlay.outgoing_slice(&addr) {
                set.insert(*to);
            }
        }
        Incoming => {
            for (from, _e) in overlay.incoming_slice(&addr) {
                set.insert(*from);
            }
        }
    }

    map.insert(addr, set);
}

fn get_neighbors_cached_bucket<'a>(
    caches: &'a BlockCaches,
    addr: Address,
    dir: petgraph::Direction,
) -> &'a FxHashSet<Address> {
    let map = match dir {
        Incoming => &caches.neighbors_in,
        Outgoing => &caches.neighbors_out,
    };

    map.get(&addr).expect("neighbors not cached")
}

fn update_neighbor_cache_for_edge_bucket(
    caches: &mut BlockCaches,
    from: Address,
    to: Address,
) {
    caches.neighbors_out.entry(from).or_default().insert(to);
    caches.neighbors_in.entry(to).or_default().insert(from);
}

fn neighbors_to_vec_with_ephemeral_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    overlay: &BlockOverlay,
    caches: &mut BlockCaches,
    addr: Address,
    dir: petgraph::Direction,
    ephemeral: Option<(Address, Address, &TransferEdge)>,
    out: &mut Vec<Address>,
) {
    ensure_neighbors_cached_bucket(graph, node_map, overlay, caches, addr, dir);

    out.clear();

    let cached = get_neighbors_cached_bucket(caches, addr, dir);

    if out.capacity() < cached.len() {
        out.reserve(cached.len().saturating_sub(out.capacity()));
    }

    out.extend(cached.iter().copied());

    if let Some((efrom, eto, _)) = ephemeral {
        match dir {
            Incoming if eto == addr => {
                if !cached.contains(&efrom) {
                    out.push(efrom);
                }
            }
            Outgoing if efrom == addr => {
                if !cached.contains(&eto) {
                    out.push(eto);
                }
            }
            _ => {}
        }
    }
}

// ============================================================================
// Motif checks over shared graph + bucket-local overlay/cache
// ============================================================================

fn check_motifs_against_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    overlay: &BlockOverlay,
    caches: &mut BlockCaches,
    config: &Config,
    to_addr: Address,
    current_block: u64,
    ephemeral: Option<(Address, Address, &TransferEdge)>,
) -> MotifResult {
    let mut result = MotifResult::default();

    let mut incoming = Vec::new();

    neighbors_to_vec_with_ephemeral_bucket(
        graph,
        node_map,
        overlay,
        caches,
        to_addr,
        Incoming,
        ephemeral,
        &mut incoming,
    );

    // 1) FAN-IN
    let mut fan_in_count = 0u64;
    let mut fan_in_sum = U256::ZERO;

    for &src_addr in &incoming {
        let (neighbor_total, _maxb) = window_sum_full_bucket(
            graph,
            node_map,
            overlay,
            caches,
            config,
            src_addr,
            to_addr,
            current_block,
            ephemeral,
        );

        if neighbor_total > U256::ZERO {
            fan_in_count += 1;
            fan_in_sum += neighbor_total;

            if fan_in_count > config.fan_in_count_threshold
                || fan_in_sum > config.fan_in_sum_threshold
            {
                result.fan_in = true;
                return result;
            }
        }
    }

    // 2) SCATTER-GATHER
    let mut source_data: FxHashMap<Address, (u64, U256)> = FxHashMap::default();

    for &inter_addr in &incoming {
        let (inter_to_dest_sum, inter_to_dest_max) = window_sum_full_bucket(
            graph,
            node_map,
            overlay,
            caches,
            config,
            inter_addr,
            to_addr,
            current_block,
            ephemeral,
        );

        if inter_to_dest_sum == U256::ZERO {
            continue;
        }

        let mut srcs = Vec::new();

        // Same as baseline: no ephemeral when collecting incoming neighbors of
        // intermediary. The current edge is still considered by pair-sum calls
        // where relevant.
        neighbors_to_vec_with_ephemeral_bucket(
            graph,
            node_map,
            overlay,
            caches,
            inter_addr,
            Incoming,
            None,
            &mut srcs,
        );

        for src_addr in srcs.into_iter() {
            let (src_to_inter_sum, src_to_inter_max) = window_sum_full_bucket(
                graph,
                node_map,
                overlay,
                caches,
                config,
                src_addr,
                inter_addr,
                current_block,
                ephemeral,
            );

            if src_to_inter_sum == U256::ZERO {
                continue;
            }

            if src_to_inter_max <= inter_to_dest_max {
                let bottleneck = src_to_inter_sum.min(inter_to_dest_sum);
                let entry = source_data.entry(src_addr).or_insert((0, U256::ZERO));

                entry.0 += 1;
                entry.1 += bottleneck;
            }
        }
    }

    for (_src, (inter_count, total_flow)) in source_data.into_iter() {
        if inter_count > config.scatter_gather_count_threshold
            && total_flow > config.scatter_gather_threshold
        {
            result.scatter_gather = true;
            return result;
        }
    }

    result
}

fn check_motifs_from_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    overlay: &BlockOverlay,
    caches: &mut BlockCaches,
    config: &Config,
    from_addr: Address,
    current_block: u64,
    ephemeral: Option<(Address, Address, &TransferEdge)>,
) -> MotifResult {
    let mut result = MotifResult::default();

    // 1) FAN-OUT
    let mut destinations = Vec::new();

    neighbors_to_vec_with_ephemeral_bucket(
        graph,
        node_map,
        overlay,
        caches,
        from_addr,
        Outgoing,
        ephemeral,
        &mut destinations,
    );

    let mut fan_out_count = 0u64;
    let mut fan_out_sum = U256::ZERO;

    for recv_addr in destinations.into_iter() {
        let (neighbor_total, _maxb) = window_sum_full_bucket(
            graph,
            node_map,
            overlay,
            caches,
            config,
            from_addr,
            recv_addr,
            current_block,
            ephemeral,
        );

        if neighbor_total > U256::ZERO {
            fan_out_count += 1;
            fan_out_sum += neighbor_total;

            if fan_out_count > config.fan_out_count_threshold
                || fan_out_sum > config.fan_out_sum_threshold
            {
                result.fan_out = true;
                return result;
            }
        }
    }

    // 2) GATHER-SCATTER
    let mut sources = Vec::new();

    neighbors_to_vec_with_ephemeral_bucket(
        graph,
        node_map,
        overlay,
        caches,
        from_addr,
        Incoming,
        ephemeral,
        &mut sources,
    );

    let sources_len = sources.len();
    let mut incoming_sum = U256::ZERO;

    for src_addr in sources.into_iter() {
        let (sum, _maxb) = window_sum_full_bucket(
            graph,
            node_map,
            overlay,
            caches,
            config,
            src_addr,
            from_addr,
            current_block,
            ephemeral,
        );

        incoming_sum += sum;
    }

    let flow_volume = incoming_sum.min(fan_out_sum);

    if sources_len as u64 > config.gather_scatter_count_threshold
        && fan_out_count > config.gather_scatter_count_threshold
        && flow_volume > config.gather_scatter_threshold
    {
        result.gather_scatter = true;
        return result;
    }

    result
}

fn would_be_suspicious_bucket(
    graph: &StableGraph<Address, TransferEdge>,
    node_map: &FxHashMap<Address, NodeIndex>,
    overlay: &BlockOverlay,
    caches: &mut BlockCaches,
    config: &Config,
    from: Address,
    to: Address,
    amount: U256,
    block: u64,
) -> (MotifResult, MotifResult) {
    let edge = TransferEdge { amount, block };
    let ephemeral = Some((from, to, &edge));

    let suspicious_from = check_motifs_from_bucket(
        graph,
        node_map,
        overlay,
        caches,
        config,
        from,
        block,
        ephemeral,
    );

    if suspicious_from.is_suspicious() {
        return (suspicious_from, MotifResult::default());
    }

    let suspicious_to = check_motifs_against_bucket(
        graph,
        node_map,
        overlay,
        caches,
        config,
        to,
        block,
        ephemeral,
    );

    (suspicious_from, suspicious_to)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, Bytes, U256};
    use std::str::FromStr;
    use std::time::Instant;
    use alloy_consensus::private::alloy_rlp::Decodable;
    use alloy_consensus::transaction::SignerRecoverable;
    use alloy_consensus::{Transaction, TxEnvelope};
    // use rand::rngs::StdRng;
    // use rand::{Rng, SeedableRng};

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
            gather_scatter_count_threshold: 3,
            scatter_gather_count_threshold: 3,
        }
    }

    fn same_bucket(buckets: &[Vec<usize>], a: usize, b: usize) -> bool {
        buckets
            .iter()
            .any(|bucket| bucket.contains(&a) && bucket.contains(&b))
    }

    fn bucket_sizes(mut buckets: Vec<Vec<usize>>) -> Vec<usize> {
        let mut sizes: Vec<usize> = buckets.drain(..).map(|b| b.len()).collect();
        sizes.sort_unstable();
        sizes
    }

    fn mk_tx(from: Address, to: Address, amount: u64) -> (Address, Address, Address, U256) {
        (ZERO_ADDRESS, from, to, U256::from(amount))
    }

    fn commit_history(
        d: &mut AMLMotifDetector,
        block: u64,
        txs: &[(Address, Address, Address, U256)],
    ) {
        d.block_commit(block, parent_hash(block - 1), txs);
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
        let r1 = addr("0x2000000000000000000000000000000000000002");
        let r2 = addr("0x2000000000000000000000000000000000000003");
        assert!(!d2.proposer_check_tx(src, r1, U256::from(6), ZERO_ADDRESS, 10, parent_hash(9)));
        // Next edge causes fan-out count >= 2 and sum 12 > 10 -> suspicious
        assert!(d2.proposer_check_tx(src, r2, U256::from(6), ZERO_ADDRESS, 10, parent_hash(9)));
    }

    // --------------------------------
    // 2) Scatter-gather & Gather-scatter
    // --------------------------------
    #[test]
    fn aml_scatter_gather_and_gather_scatter() {
        let mut d = AMLMotifDetector::new(cfg());
        let source = addr("0x3000000000000000000000000000000000000001");
        let i1 = addr("0x3000000000000000000000000000000000000002");
        let i2 = addr("0x3000000000000000000000000000000000000003");
        let sink = addr("0x30000000000000000000000000000000000000aa");

        // Scatter-gather: source -> i1 -> sink, source -> i2 -> sink
        assert!(!d.proposer_check_tx(source, i1, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d.proposer_check_tx(i1, sink, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d.proposer_check_tx(source, i2, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        // This final edge should trigger (bottlenecks sum to 10 > 8)
        assert!(d.proposer_check_tx(i2, sink, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));

        // Gather-scatter (hub): multiple sources -> hub -> one receiver
        let mut d2 = AMLMotifDetector::new(cfg());
        let s1 = addr("0x4000000000000000000000000000000000000001");
        let s2 = addr("0x4000000000000000000000000000000000000002");
        let hub = addr("0x40000000000000000000000000000000000000bb");
        let recv = addr("0x40000000000000000000000000000000000000bc");
        assert!(!d2.proposer_check_tx(s1, hub, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        assert!(!d2.proposer_check_tx(s2, hub, U256::from(5), ZERO_ADDRESS, 10, parent_hash(9)));
        // Hub to receiver (sum bottlenecks = 10 > threshold 8)
        assert!(d2.proposer_check_tx(hub, recv, U256::from(10), ZERO_ADDRESS, 10, parent_hash(9)));
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
        assert!(d.consensus_validate_block(&txs, block, parent_hash(block - 1)).len() > 0);
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
        let r1 = addr("0x2000000000000000000000000000000000000002");
        let r2 = addr("0x2000000000000000000000000000000000000003");

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
        let r1 = addr("0x2100000000000000000000000000000000000002");
        let r2 = addr("0x2100000000000000000000000000000000000003");

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
        let i1 = addr("0x3000000000000000000000000000000000000002");
        let i2 = addr("0x3000000000000000000000000000000000000003");
        let sink = addr("0x30000000000000000000000000000000000000aa");
        let block = 40;
        let phash = parent_hash(block - 1);

        // Build the paths incrementally using proposer (overlay-only)
        assert!(!d.proposer_check_tx(source, i1, U256::from(5), ZERO_ADDRESS, block, phash));
        assert!(!d.proposer_check_tx(i1, sink, U256::from(5), ZERO_ADDRESS, block, phash));
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
        let s1 = addr("0x4000000000000000000000000000000000000001");
        let s2 = addr("0x4000000000000000000000000000000000000002");
        let hub = addr("0x40000000000000000000000000000000000000bb");
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
        let r1 = addr("0x6000000000000000000000000000000000000002");
        let r2 = addr("0x6000000000000000000000000000000000000003");

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
        let s1 = addr("0x8000000000000000000000000000000000000001");
        let s2 = addr("0x8000000000000000000000000000000000000002");
        let s3 = addr("0x8000000000000000000000000000000000000003");

        // Commit two prior blocks with sender->sink edges inside window
        for blk in 90..=91 {
            let txs = vec![(ZERO_ADDRESS, if blk == 90 { s1 } else { s2 }, sink, U256::from(5))];
            assert!(d.consensus_validate_block(&txs, blk, parent_hash(blk - 1)).is_empty());
            d.block_commit(blk, parent_hash(blk - 1), &txs);
        }
        assert_eq!(d.graph.edge_count(), 2);

        // At current block 92 (within window_blocks=5), adding s3->sink(1) should tip fan-in sum 11 > 10
        let current = 92;
        let phash = parent_hash(current - 1);
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

    const TOKEN_SYMBOL: &str = "USDC";

    /// Smallest unit = 10^TOKEN_DECIMALS raw units = 1 whole token.
    /// USDC/USDT = 6, WBTC = 8, DAI/WETH/most ERC-20s = 18.
    const TOKEN_DECIMALS: u32 = 6;

    // -----------------------------------------------------------------------
    // CSV parsing
    // -----------------------------------------------------------------------

    #[derive(Debug)]
    struct CsvRecord {
        block_number: u64,
        raw_tx: String,
    }

    fn read_transfer_csv(path: &str) -> Vec<CsvRecord> {
        let mut rdr = csv::Reader::from_path(path)
            .unwrap_or_else(|e| panic!("Cannot open CSV at {path}: {e}"));

        let mut records = Vec::new();
        for result in rdr.records() {
            let r = result.expect("bad CSV row");
            let block_number: u64 = r[0].trim().parse().expect("block_number must be u64");
            let raw_tx = r[1].trim().to_string();
            records.push(CsvRecord { block_number, raw_tx });
        }
        records
    }

    // -----------------------------------------------------------------------
    // Raw-tx decoding
    // -----------------------------------------------------------------------

    fn hex_to_bytes(s: &str) -> Vec<u8> {
        let s = s.strip_prefix("0x").unwrap_or(s);
        hex::decode(s).unwrap_or_else(|e| panic!("hex decode failed: {e}"))
    }

    /// ERC-20 transfer(address,uint256) calldata layout:
    ///   [0..4]   selector  = 0xa9059cbb
    ///   [4..36]  to        = 32-byte padded address (actual addr at [16..36])
    ///   [36..68] amount    = 32-byte big-endian uint256
    fn decode_erc20_transfer(input: &[u8]) -> Option<(Address, U256)> {
        const SELECTOR: [u8; 4] = [0xa9, 0x05, 0x9c, 0xbb];
        if input.len() < 68 || input[..4] != SELECTOR {
            return None;
        }
        let to = Address::from_slice(&input[16..36]);
        let amount = U256::from_be_slice(&input[36..68]);
        Some((to, amount))
    }

    fn decode_tx(record: &CsvRecord) -> Option<(Address, Address, Address, U256)> {
        let raw = hex_to_bytes(&record.raw_tx);
        let mut buf = raw.as_slice();

        let envelope = TxEnvelope::decode(&mut buf)
            .map_err(|e| eprintln!("block {}: RLP decode failed: {e}", record.block_number))
            .ok()?;

        let from = envelope
            .recover_signer()
            .map_err(|e| eprintln!("block {}: signer recovery failed: {e}", record.block_number))
            .ok()?;

        let token = *envelope.to()?;
        let input: &Bytes = envelope.input();
        let (to, amount) = decode_erc20_transfer(input)?;

        Some((Address::from(token), from, to, amount))
    }

    // -----------------------------------------------------------------------
    // Scaling helpers
    // -----------------------------------------------------------------------

    /// Returns 10^TOKEN_DECIMALS as U256 — i.e. 1 whole token in raw on-chain units.
    fn one_token() -> U256 {
        U256::from(10u64.pow(TOKEN_DECIMALS))
    }

    /// Convert a human-readable whole-token amount to raw on-chain units.
    ///
    /// Examples with TOKEN_DECIMALS=6 (USDC):
    ///   tokens(1_000)     →  1_000_000_000        (= $1,000 USDC)
    ///   tokens(100_000)   →  100_000_000_000      (= $100,000 USDC)
    ///   tokens(1_000_000) →  1_000_000_000_000    (= $1,000,000 USDC)
    fn tokens(whole: u128) -> U256 {
        // U256::from(whole) * one_token()
        U256::from(whole)
    }

    // -----------------------------------------------------------------------
    // Config sweep definition
    //
    // All `*_sum` fields are in WHOLE TOKENS (human-readable dollar amounts
    // for stablecoins). `tokens()` converts to raw on-chain units inside
    // `make_config`, so you never have to count zeros manually.
    // -----------------------------------------------------------------------

    struct SweepConfig {
        label: &'static str,
        window_blocks: u64,
        // fan-in (smurfing: many senders → one sink)
        fan_in_count: u64,   // distinct sender threshold
        fan_in_sum: u128,    // total inflow threshold, whole tokens
        // fan-out (dispersal: one source → many receivers)
        fan_out_count: u64,  // distinct receiver threshold
        fan_out_sum: u128,   // total outflow threshold, whole tokens
        // scatter-gather (source → intermediaries → sink)
        sg_count: u64,       // intermediary count threshold
        sg_sum: u128,        // bottleneck flow threshold, whole tokens
        // gather-scatter (sources → hub → receivers)
        gs_count: u64,       // source/receiver count threshold
        gs_sum: u128,        // flow volume threshold, whole tokens
    }

    fn make_config(s: &SweepConfig) -> Config {
        Config {
            window_blocks: s.window_blocks,
            fan_in_count_threshold: s.fan_in_count,
            fan_in_sum_threshold: tokens(s.fan_in_sum),
            fan_out_count_threshold: s.fan_out_count,
            fan_out_sum_threshold: tokens(s.fan_out_sum),
            scatter_gather_threshold: tokens(s.sg_sum),
            scatter_gather_count_threshold: s.sg_count,
            gather_scatter_threshold: tokens(s.gs_sum),
            gather_scatter_count_threshold: s.gs_count,
        }
    }

    // -----------------------------------------------------------------------
    // Per-config run
    // -----------------------------------------------------------------------

    #[derive(Default, Debug)]
    struct RunResult {
        total_txs: usize,
        flagged_fan_in: u64,
        flagged_fan_out: u64,
        flagged_scatter_gather: u64,
        flagged_gather_scatter: u64,
        total_flagged: usize,
    }

    fn run_sweep(
        decoded: &[(u64, (Address, Address, Address, U256))],
        config: Config,
    ) -> RunResult {
        let mut detector = AMLMotifDetector::new(config);
        let mut result = RunResult {
            total_txs: decoded.len(),
            ..Default::default()
        };

        let parent_hash_for = |b: u64| -> B256 {
            let mut bytes = [0u8; 32];
            bytes[24..].copy_from_slice(&b.to_be_bytes());
            B256::from(bytes)
        };

        let mut current_block: u64 = 0;
        let mut pending_commit: Vec<(Address, Address, Address, U256)> = Vec::new();

        for &(block, (token, from, to, amount)) in decoded {
            // Commit the completed block before moving to the next one
            if block != current_block && current_block != 0 {
                let phash = parent_hash_for(current_block.saturating_sub(1));
                detector.block_commit(current_block, phash, &pending_commit);
                pending_commit.clear();
            }
            current_block = block;

            let phash = parent_hash_for(block.saturating_sub(1));
            let flagged = detector.proposer_check_tx(from, to, amount, token, block, phash);

            if flagged {
                // Re-probe with an ephemeral edge to categorise which motif fired.
                // proposer_check_tx only returns bool; this gives us the breakdown.
                let edge = TransferEdge { amount, block };
                let eph = Some((from, to, &edge));

                let from_result = detector.check_motifs_from_view_ephemeral(from, block, eph);
                let to_result = detector.check_motifs_against_view_ephemeral(to, block, eph);

                if from_result.fan_out { result.flagged_fan_out += 1; }
                if from_result.gather_scatter { result.flagged_gather_scatter += 1; }
                if to_result.fan_in { result.flagged_fan_in += 1; }
                if to_result.scatter_gather { result.flagged_scatter_gather += 1; }

                result.total_flagged += 1;
            } else {
                pending_commit.push((token, from, to, amount));
            }
        }

        // Commit the final block
        if current_block != 0 && !pending_commit.is_empty() {
            let phash = parent_hash_for(current_block.saturating_sub(1));
            detector.block_commit(current_block, phash, &pending_commit);
        }

        result
    }

    // -----------------------------------------------------------------------
    // Print helpers
    // -----------------------------------------------------------------------

    fn print_table(configs: &[SweepConfig], results: &[RunResult]) {
        let total = results.first().map(|r| r.total_txs).unwrap_or(0);

        println!("\n{}", "=".repeat(120));
        println!(
            "Token: {}  (decimals={})  |  sum thresholds below are in whole {} (e.g. 100_000 = {} 100k)",
            TOKEN_SYMBOL, TOKEN_DECIMALS, TOKEN_SYMBOL, TOKEN_SYMBOL,
        );
        println!("{}", "=".repeat(120));
        println!(
            "{:<30}  {:>5}  {:>7}/{:<10}  {:>7}/{:<10}  {:>5}/{:<10}  {:>5}/{:<10}  {:>7}  {:>6}  breakdown",
            "config", "w",
            "fi_n", "fi_sum($)",
            "fo_n", "fo_sum($)",
            "sg_n", "sg_sum($)",
            "gs_n", "gs_sum($)",
            "flagged", "pct%",
        );
        println!("{}", "-".repeat(120));

        for (cfg, res) in configs.iter().zip(results.iter()) {
            let pct = 100.0 * res.total_flagged as f64 / total.max(1) as f64;
            println!(
                "{:<30}  {:>5}  {:>7}/{:<10}  {:>7}/{:<10}  {:>5}/{:<10}  {:>5}/{:<10}  {:>7}  {:>5.2}%  fi={} fo={} sg={} gs={}",
                cfg.label,
                cfg.window_blocks,
                cfg.fan_in_count, cfg.fan_in_sum,
                cfg.fan_out_count, cfg.fan_out_sum,
                cfg.sg_count, cfg.sg_sum,
                cfg.gs_count, cfg.gs_sum,
                res.total_flagged,
                pct,
                res.flagged_fan_in,
                res.flagged_fan_out,
                res.flagged_scatter_gather,
                res.flagged_gather_scatter,
            );
        }

        println!("{}", "=".repeat(120));
        println!("Total decoded txs: {total}");
    }

    // -----------------------------------------------------------------------
    // The test
    // -----------------------------------------------------------------------

    /// Run with:
    ///   cargo test sweep_configs -- --nocapture
    ///
    /// Point at your CSV via env var (default: data/transfers.csv):
    ///   AML_CSV=path/to/file.csv cargo test sweep_configs -- --nocapture
    ///
    /// CSV format expected:
    ///   block_number,raw_tx
    ///   20000000,0x02f8...
    #[test]
    fn sweep_configs() {
        let csv_path = "/home/shehs/working_dir/ronaldo_testing/Throughput_testing/hash_csv_input_full.csv";

        println!("\nLoading CSV from: {csv_path}");
        let records = read_transfer_csv(&csv_path);
        println!("Loaded {} raw records", records.len());

        let mut decoded: Vec<(u64, (Address, Address, Address, U256))> = Vec::new();
        let mut skipped = 0usize;
        for rec in &records {
            match decode_tx(rec) {
                Some(tuple) => decoded.push((rec.block_number, tuple)),
                None => skipped += 1,
            }
        }
        println!(
            "Decoded {} ERC-20 transfers ({} skipped: non-transfer calldata or decode failure)\n",
            decoded.len(),
            skipped,
        );

        if decoded.is_empty() {
            println!("No decodable ERC-20 transfers found — check TOKEN_DECIMALS and CSV format.");
            return;
        }

        // ------------------------------------------------------------------
        // Sweep table — edit sum values as whole token amounts.
        //
        // Tuning guide (watch the flagged% column):
        //   < 0.01%  →  thresholds too loose; tighten counts or sums
        //   0.1–5%   →  good regime for real AML signal
        //   > 20%    →  thresholds too tight; loosen
        //
        // Most sensitive knob for frequency-based patterns: fan_in_count / fan_out_count
        // Most sensitive knob for value-based patterns:     fan_in_sum   / fan_out_sum
        // ------------------------------------------------------------------
        let sweep: Vec<SweepConfig> = vec![
            // Row 1: Loose — only catches extreme high-volume outliers
            // Row 1: Conservative — only extreme outliers
            SweepConfig {
                label: "conservative",
                window_blocks: 300,
                fan_in_count: 1000,
                fan_in_sum: 10000000000000,
                fan_out_count: 1000,
                fan_out_sum: 10000000000000,
                sg_count: 5,
                sg_sum: 25000000000,
                gs_count: 5,
                gs_sum: 25000000000,   // keep gs thresholds fixed
            },
            // Row 2: Moderate
            SweepConfig {
                label: "moderate",
                window_blocks: 300,
                fan_in_count: 50,
                fan_in_sum: 10000000000000,
                fan_out_count: 50,
                fan_out_sum: 10000000000000,
                sg_count: 1000,
                sg_sum: 10000000000000,
                gs_count: 1000,
                gs_sum: 10000000000000,
            },
            // Row 3: sg/gs focused — your existing anchor
            SweepConfig {
                label: "scatter_gather_focused",
                window_blocks: 300,
                fan_in_count: 1_000,
                fan_in_sum: 100000000000,
                fan_out_count: 1_000,
                fan_out_sum: 100000000000,
                sg_count: 1000,
                sg_sum: 10000000000000,
                gs_count: 1000,
                gs_sum: 10000000000000,
            },
            // Row 4: fi/fo focused — frequency driven
            SweepConfig {
                label: "fan_frequency",
                window_blocks: 300,
                fan_in_count: 100,
                fan_in_sum: 1000000000000,
                fan_out_count: 100,
                fan_out_sum: 1000000000000,
                sg_count: 5,
                sg_sum: 50000000000,  // effectively disabled
                gs_count: 5,
                gs_sum: 50000000000,
            },
            // Row 5: fi/fo focused — value driven
            SweepConfig {
                label: "fan_value",
                window_blocks: 300,
                fan_in_count: 1_000,
                fan_in_sum: 100_000,
                fan_out_count: 1_000,
                fan_out_sum: 100_000,
                sg_count: 1_000,
                sg_sum: 10_000_000,  // effectively disabled
                gs_count: 1_000,
                gs_sum: 10_000_000,
            },
        ];

        let mut results: Vec<RunResult> = Vec::with_capacity(sweep.len());

        for cfg in &sweep {
            print!("  Running '{}'... ", cfg.label);
            let result = run_sweep(&decoded, make_config(cfg));
            println!(
                "{}/{} flagged ({:.2}%)  [fi={} fo={} sg={} gs={}]",
                result.total_flagged,
                result.total_txs,
                100.0 * result.total_flagged as f64 / result.total_txs.max(1) as f64,
                result.flagged_fan_in,
                result.flagged_fan_out,
                result.flagged_scatter_gather,
                result.flagged_gather_scatter,
            );
            results.push(result);
        }

        print_table(&sweep, &results);
    }


    ////////////////////////////////////////////////////////////////////////////


    // -----------------------------------------------------------------------
    // Synthetic injection detectability test (GROUP-level counting)
    // - Detection is counted once per injected group (first-fire).
    // - We still verify which motif actually fired via re-probe.
    // - Re-probe mirrors would_be_suspicious(): sender-side first, early return.
    // -----------------------------------------------------------------------

    const BENIGN_TX_COUNT: usize = 10_000;
    const GROUPS_PER_MOTIF: usize = 100;
    const BLOCK_SIZE: usize = 100;

    // Address-space constants
    const INJECT_ADDR_BASE: u64 = 1_000_000;

    // -----------------------------------------------------------------------
    // Helper: synthetic address from a u64 seed
    // -----------------------------------------------------------------------
    fn addr2(seed: u64) -> Address {
        let mut bytes = [0u8; 20];
        bytes[12..].copy_from_slice(&seed.to_be_bytes());
        Address::from(bytes)
    }

    // -----------------------------------------------------------------------
    // Helper: fake ERC-20 token address
    // -----------------------------------------------------------------------
    fn token_addr() -> Address {
        addr2(0xDEAD_BEEF_u64)
    }

    // -----------------------------------------------------------------------
    // Labels
    // -----------------------------------------------------------------------
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum MotifKind {
        FanIn,
        FanOut,
        ScatterGather,
        GatherScatter,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct GroupId(u32);

    #[derive(Debug, Clone, Copy)]
    struct GroupMeta {
        kind: MotifKind,
    }

    // -----------------------------------------------------------------------
    // Synthetic tx
    // -----------------------------------------------------------------------
    #[derive(Debug, Clone)]
    struct SyntheticTx {
        seq: u64,
        block: u64,
        token: Address,
        from: Address,
        to: Address,
        amount: U256,

        // None for benign traffic
        group: Option<GroupId>,
    }

    // -----------------------------------------------------------------------
    // Strength shaping (deterministic heterogeneity)
    //   We want thresholds sweeps to produce partial detectability.
    //   So groups of each motif are generated with varying k.
    // -----------------------------------------------------------------------

    fn bucket5(i: usize) -> i64 {
        match i % 5 {
            0 => -2,
            1 => -1,
            2 => 0,
            3 => 1,
            _ => 2,
        }
    }

    fn clamp_u64(x: i64, lo: u64, hi: u64) -> u64 {
        let x = if x < lo as i64 { lo as i64 } else if x > hi as i64 { hi as i64 } else { x };
        x as u64
    }

    // We keep disjoint bands:
    // - SG/GS use a small k band.
    // - FI/FO use a much larger k band.
    const K_SG_BASE: u64 = 6;   // SG/GS groups will vary around this within [2..10]
    const K_FI_BASE: u64 = 26;  // FI/FO groups will vary around this within [18..34]

    const K_SG_MIN: u64 = 3;
    const K_SG_MAX: u64 = 10;
    const K_FI_MIN: u64 = 18;
    const K_FI_MAX: u64 = 34;

    // Per-edge amounts (keep simple; we primarily sweep count thresholds).
    const AMT_FAN: u64 = 10;
    const AMT_HOP: u64 = 5;

    // -----------------------------------------------------------------------
    // Injection generators (disjoint by construction)
    // -----------------------------------------------------------------------

    fn gen_fan_in_group(gid: GroupId, base_block: u64, k: u64, addr_offset: &mut u64) -> Vec<SyntheticTx> {
        let receiver = addr2(INJECT_ADDR_BASE + *addr_offset);
        *addr_offset += 1;

        let amount = U256::from(AMT_FAN);
        let mut txs = Vec::with_capacity(k as usize);

        for i in 0..k {
            let sender = addr2(INJECT_ADDR_BASE + *addr_offset + i);
            txs.push(SyntheticTx {
                seq: 0,
                block: base_block + (i / BLOCK_SIZE as u64),
                token: token_addr(),
                from: sender,
                to: receiver,
                amount,
                group: Some(gid),
            });
        }
        *addr_offset += k;
        txs
    }

    fn gen_fan_out_group(gid: GroupId, base_block: u64, k: u64, addr_offset: &mut u64) -> Vec<SyntheticTx> {
        let sender = addr2(INJECT_ADDR_BASE + *addr_offset);
        *addr_offset += 1;

        let amount = U256::from(AMT_FAN);
        let mut txs = Vec::with_capacity(k as usize);

        for i in 0..k {
            let receiver = addr2(INJECT_ADDR_BASE + *addr_offset + i);
            txs.push(SyntheticTx {
                seq: 0,
                block: base_block + (i / BLOCK_SIZE as u64),
                token: token_addr(),
                from: sender,
                to: receiver,
                amount,
                group: Some(gid),
            });
        }
        *addr_offset += k;
        txs
    }

    // Two-phase SG: all source->mid first, then all mid->sink
    fn gen_scatter_gather_group(gid: GroupId, base_block: u64, k: u64, addr_offset: &mut u64) -> Vec<SyntheticTx> {
        let source = addr2(INJECT_ADDR_BASE + *addr_offset);
        *addr_offset += 1;
        let sink = addr2(INJECT_ADDR_BASE + *addr_offset);
        *addr_offset += 1;

        let mut mids = Vec::with_capacity(k as usize);
        for i in 0..k {
            mids.push(addr2(INJECT_ADDR_BASE + *addr_offset + i));
        }
        *addr_offset += k;

        let amount = U256::from(AMT_HOP);
        let mut txs = Vec::with_capacity((2 * k) as usize);

        // phase 1
        for (i, mid) in mids.iter().copied().enumerate() {
            txs.push(SyntheticTx {
                seq: 0,
                block: base_block + (i as u64 / BLOCK_SIZE as u64),
                token: token_addr(),
                from: source,
                to: mid,
                amount,
                group: Some(gid),
            });
        }

        // phase 2
        for (i, mid) in mids.into_iter().enumerate() {
            txs.push(SyntheticTx {
                seq: 0,
                block: base_block + ((k + i as u64) / BLOCK_SIZE as u64),
                token: token_addr(),
                from: mid,
                to: sink,
                amount,
                group: Some(gid),
            });
        }

        txs
    }

    // Two-phase GS: all sources->hub first, then hub->receivers
    fn gen_gather_scatter_group(gid: GroupId, base_block: u64, k: u64, addr_offset: &mut u64) -> Vec<SyntheticTx> {
        let hub = addr2(INJECT_ADDR_BASE + *addr_offset);
        *addr_offset += 1;

        let mut sources = Vec::with_capacity(k as usize);
        let mut receivers = Vec::with_capacity(k as usize);

        for i in 0..k {
            sources.push(addr2(INJECT_ADDR_BASE + *addr_offset + i));
            receivers.push(addr2(INJECT_ADDR_BASE + *addr_offset + k + i));
        }
        *addr_offset += 2 * k;

        let amount = U256::from(AMT_HOP);
        let mut txs = Vec::with_capacity((2 * k) as usize);

        // phase 1
        for (i, src) in sources.iter().copied().enumerate() {
            txs.push(SyntheticTx {
                seq: 0,
                block: base_block + (i as u64 / BLOCK_SIZE as u64),
                token: token_addr(),
                from: src,
                to: hub,
                amount,
                group: Some(gid),
            });
        }

        // phase 2
        for (i, rcv) in receivers.into_iter().enumerate() {
            txs.push(SyntheticTx {
                seq: 0,
                block: base_block + ((k + i as u64) / BLOCK_SIZE as u64),
                token: token_addr(),
                from: hub,
                to: rcv,
                amount,
                group: Some(gid),
            });
        }

        txs
    }

    // -----------------------------------------------------------------------
    // Dataset assembly
    // -----------------------------------------------------------------------

    fn build_dataset() -> (Vec<SyntheticTx>, Vec<GroupMeta>) {
        let mut addr_offset: u64 = 0;

        let total_groups = 4 * GROUPS_PER_MOTIF;
        let mut groups: Vec<GroupMeta> = Vec::with_capacity(total_groups);
        let mut injected: Vec<SyntheticTx> = Vec::new();

        // Start injections at block 1 (avoid genesis edge-case).
        let mut next_base_block: u64 = 1;

        // Helper to allocate group ids consecutively and keep groups vector indexable by id.
        let mut gid_u32: u32 = 0;
        let mut new_group = |kind: MotifKind| -> GroupId {
            let gid = GroupId(gid_u32);
            gid_u32 += 1;
            groups.push(GroupMeta { kind });
            gid
        };

        // FI groups: high k band
        for i in 0..GROUPS_PER_MOTIF {
            let gid = new_group(MotifKind::FanIn);
            let k = clamp_u64(K_FI_BASE as i64 + bucket5(i) * 4, K_FI_MIN, K_FI_MAX);
            injected.extend(gen_fan_in_group(gid, next_base_block, k, &mut addr_offset));
            next_base_block += 1;
        }

        // FO groups: high k band
        for i in 0..GROUPS_PER_MOTIF {
            let gid = new_group(MotifKind::FanOut);
            let k = clamp_u64(K_FI_BASE as i64 + bucket5(i) * 4, K_FI_MIN, K_FI_MAX);
            injected.extend(gen_fan_out_group(gid, next_base_block, k, &mut addr_offset));
            next_base_block += 1;
        }

        // SG groups: low k band
        for i in 0..GROUPS_PER_MOTIF {
            let gid = new_group(MotifKind::ScatterGather);
            let k = clamp_u64(K_SG_BASE as i64 + bucket5(i) * 2, K_SG_MIN, K_SG_MAX);
            injected.extend(gen_scatter_gather_group(gid, next_base_block, k, &mut addr_offset));
            next_base_block += 1;
        }

        // GS groups: low k band
        for i in 0..GROUPS_PER_MOTIF {
            let gid = new_group(MotifKind::GatherScatter);
            let k = clamp_u64(K_SG_BASE as i64 + bucket5(i) * 2, K_SG_MIN, K_SG_MAX);
            injected.extend(gen_gather_scatter_group(gid, next_base_block, k, &mut addr_offset));
            next_base_block += 1;
        }

        // Benign: fresh addresses per tx => motifs impossible by construction
        let mut benign: Vec<SyntheticTx> = Vec::with_capacity(BENIGN_TX_COUNT);
        for i in 0..BENIGN_TX_COUNT {
            let block = i as u64 / BLOCK_SIZE as u64;
            benign.push(SyntheticTx {
                seq: 0,
                block,
                token: token_addr(),
                from: addr2(0xB000_0000u64 + 2 * i as u64),
                to: addr2(0xB000_0000u64 + 2 * i as u64 + 1),
                amount: U256::from(1u64),
                group: None,
            });
        }

        let mut all: Vec<SyntheticTx> = Vec::with_capacity(injected.len() + benign.len());
        all.append(&mut injected);
        all.append(&mut benign);

        // Deterministic tiebreaker
        for (i, tx) in all.iter_mut().enumerate() {
            tx.seq = i as u64;
        }

        // Deterministic order: by block then seq.
        all.sort_by_key(|tx| (tx.block, tx.seq));

        (all, groups)
    }

    // -----------------------------------------------------------------------
    // Sweep configuration
    // -----------------------------------------------------------------------

    #[derive(Clone, Debug)]
    struct SweepConfig2 {
        label: &'static str,
        window_blocks: u64,

        fan_in_count: u64,
        fan_in_sum: u128,

        fan_out_count: u64,
        fan_out_sum: u128,

        sg_count: u64,
        sg_sum: u128,

        gs_count: u64,
        gs_sum: u128,
    }

    fn make_config_2(cfg: &SweepConfig2) -> Config {
        let mut c = Config {
            window_blocks: cfg.window_blocks,

            fan_in_count_threshold: cfg.fan_in_count,
            fan_in_sum_threshold: U256::from(cfg.fan_in_sum),
            scatter_gather_threshold: U256::from(cfg.sg_sum),
            scatter_gather_count_threshold: cfg.sg_count,
            gather_scatter_threshold: U256::from(cfg.gs_sum),
            gather_scatter_count_threshold: cfg.gs_count,
            fan_out_count_threshold: cfg.fan_out_count,
            fan_out_sum_threshold: U256::from(cfg.fan_out_sum),
        };

        c
    }

    // -----------------------------------------------------------------------
    // Detectability bookkeeping
    // -----------------------------------------------------------------------

    #[derive(Debug, Clone, Default)]
    struct FiredMotifs {
        fan_in: bool,
        fan_out: bool,
        scatter_gather: bool,
        gather_scatter: bool,
    }

    #[derive(Default, Debug)]
    struct DetectResult {
        total_txs: usize,

        // Number of groups detected (any flag) per intended motif.
        any_fi: usize,
        any_fo: usize,
        any_sg: usize,
        any_gs: usize,

        // Number of groups where the intended motif actually fired.
        correct_fi: usize,
        correct_fo: usize,
        correct_sg: usize,
        correct_gs: usize,

        false_positives: usize,
    }

    fn run_detectability(dataset: &[SyntheticTx], groups: &[GroupMeta], config: Config) -> DetectResult {
        let mut detector = AMLMotifDetector::new(config);

        let mut result = DetectResult {
            total_txs: dataset.len(),
            ..Default::default()
        };

        let mut correct_fi: std::collections::HashSet<GroupId> = Default::default();
        let mut correct_fo: std::collections::HashSet<GroupId> = Default::default();
        let mut correct_sg: std::collections::HashSet<GroupId> = Default::default();
        let mut correct_gs: std::collections::HashSet<GroupId> = Default::default();

        let mut any_fi: std::collections::HashSet<GroupId> = Default::default();
        let mut any_fo: std::collections::HashSet<GroupId> = Default::default();
        let mut any_sg: std::collections::HashSet<GroupId> = Default::default();
        let mut any_gs: std::collections::HashSet<GroupId> = Default::default();

        let parent_hash_for = |b: u64| -> B256 {
            let mut bytes = [0u8; 32];
            bytes[24..].copy_from_slice(&b.to_be_bytes());
            B256::from(bytes)
        };

        let mut current_block: Option<u64> = None;
        let mut pending_commit: Vec<(Address, Address, Address, U256)> = Vec::new();

        for tx in dataset {
            // commit when block changes
            if let Some(cb) = current_block {
                if tx.block != cb {
                    let phash = parent_hash_for(cb.saturating_sub(1));
                    detector.block_commit(cb, phash, &pending_commit);
                    pending_commit.clear();
                }
            }
            current_block = Some(tx.block);

            let phash = parent_hash_for(tx.block.saturating_sub(1));

            let flagged = detector.proposer_check_tx(
                tx.from, tx.to, tx.amount, tx.token, tx.block, phash,
            );

            if flagged {
                // re-probe to identify which motif actually fired
                // IMPORTANT: mirror would_be_suspicious(): check sender-side first, early return.
                let edge = TransferEdge { amount: tx.amount, block: tx.block };
                let eph = Some((tx.from, tx.to, &edge));

                let from_r = detector.check_motifs_from_view_ephemeral(tx.from, tx.block, eph);
                let to_r = if from_r.is_suspicious() {
                    MotifResult::default()
                } else {
                    detector.check_motifs_against_view_ephemeral(tx.to, tx.block, eph)
                };

                let fired = FiredMotifs {
                    fan_in: to_r.fan_in,
                    fan_out: from_r.fan_out,
                    scatter_gather: to_r.scatter_gather,
                    gather_scatter: from_r.gather_scatter,
                };

                match tx.group {
                    None => {
                        // benign flagged
                        result.false_positives += 1;
                    }
                    Some(gid) => {
                        let idx = gid.0 as usize;
                        let intended = groups[idx].kind;

                        // any-detected (flagged at all)
                        match intended {
                            MotifKind::FanIn => { any_fi.insert(gid); }
                            MotifKind::FanOut => { any_fo.insert(gid); }
                            MotifKind::ScatterGather => { any_sg.insert(gid); }
                            MotifKind::GatherScatter => { any_gs.insert(gid); }
                        }

                        // correct-detected (intended motif flag fired)
                        let correct = match intended {
                            MotifKind::FanIn => fired.fan_in,
                            MotifKind::FanOut => fired.fan_out,
                            MotifKind::ScatterGather => fired.scatter_gather,
                            MotifKind::GatherScatter => fired.gather_scatter,
                        };

                        if correct {
                            match intended {
                                MotifKind::FanIn => { correct_fi.insert(gid); }
                                MotifKind::FanOut => { correct_fo.insert(gid); }
                                MotifKind::ScatterGather => { correct_sg.insert(gid); }
                                MotifKind::GatherScatter => { correct_gs.insert(gid); }
                            }
                        }
                    }
                }
            } else {
                pending_commit.push((tx.token, tx.from, tx.to, tx.amount));
            }
        }

        // commit last block
        if let Some(cb) = current_block {
            let phash = parent_hash_for(cb.saturating_sub(1));
            detector.block_commit(cb, phash, &pending_commit);
        }

        result.correct_fi = correct_fi.len();
        result.correct_fo = correct_fo.len();
        result.correct_sg = correct_sg.len();
        result.correct_gs = correct_gs.len();

        result.any_fi = any_fi.len();
        result.any_fo = any_fo.len();
        result.any_sg = any_sg.len();
        result.any_gs = any_gs.len();

        result
    }

    // -----------------------------------------------------------------------
    // Printing
    // -----------------------------------------------------------------------

    fn print_detectability_table(configs: &[SweepConfig2], results: &[DetectResult]) {
        let n = GROUPS_PER_MOTIF as f64;

        println!("\n{}", "=".repeat(120));
        println!(
            "Detectability sweep (group-level)\nGroups per motif: {}\nBenign txs: {}",
            GROUPS_PER_MOTIF, BENIGN_TX_COUNT
        );
        println!(
            "SG/GS k ∈ [{}, {}] around base={}\nFI/FO k ∈ [{}, {}] around base={}\nblock size: {}",
            K_SG_MIN, K_SG_MAX, K_SG_BASE,
            K_FI_MIN, K_FI_MAX, K_FI_BASE,
            BLOCK_SIZE
        );
        println!("Columns: det% = correct motif fired for that group, any% = group flagged for any reason, FP = benign flagged");
        println!("{}", "=".repeat(120));
        println!(
            "{:<28} {:>7} | {:>7} {:>7} | {:>7} {:>7} | {:>7} {:>7} | {:>7} {:>7} | {:>5}",
            "config", "win",
            "FI det","FI any",
            "FO det","FO any",
            "SG det","SG any",
            "GS det","GS any",
            "FP"
        );
        println!("{}", "-".repeat(120));

        for (cfg, res) in configs.iter().zip(results.iter()) {
            let pct = |x: usize| 100.0 * (x as f64) / n;
            println!(
                "{:<28} {:>7} | {:>6.1}% {:>6.1}% | {:>6.1}% {:>6.1}% | {:>6.1}% {:>6.1}% | {:>6.1}% {:>6.1}% | {:>5}",
                cfg.label,
                cfg.window_blocks,
                pct(res.correct_fi), pct(res.any_fi),
                pct(res.correct_fo), pct(res.any_fo),
                pct(res.correct_sg), pct(res.any_sg),
                pct(res.correct_gs), pct(res.any_gs),
                res.false_positives,
            );
        }

        println!("{}", "=".repeat(120));
        println!("Legend: FI=Fan-In FO=Fan-Out SG=Scatter-Gather GS=Gather-Scatter FP=false positives");
    }

    // -----------------------------------------------------------------------
    // The test (sweep-based)
    // -----------------------------------------------------------------------

    #[test]
    fn synthetic_group_detectability_sweep() {
        let (dataset, groups) = build_dataset();

        // A disjoint, permissive baseline that should yield 4x 100% correct.
        // Key: FI/FO thresholds must be > max SG/GS k to avoid masking (FI checked before SG; FO checked before GS).
        // We also set FI/FO sum thresholds huge so only count is relevant.
        let baseline = SweepConfig2 {
            label: "minimum_disjoint (4x100)",
            window_blocks: 300,

            // FI/FO thresholds are well above SG/GS maxima to keep SG/GS disjoint.
            fan_in_count: K_SG_MAX + 1,
            fan_in_sum: u128::MAX,

            fan_out_count: K_SG_MAX + 1,
            fan_out_sum: u128::MAX,

            // SG/GS thresholds are permissive.
            sg_count: 2,
            sg_sum: 1,

            gs_count: 2,
            gs_sum: 1,
        };

        // Build a sweep that varies each motif family around its group strength band.
        // Other families stay at baseline values to preserve disjointness.
        let mut sweep: Vec<SweepConfig2> = Vec::new();
        sweep.push(baseline.clone());

        //
        // 2. Looser FI / FO
        //
        sweep.push(SweepConfig2 {
            label: "looser_FI_FO",
            window_blocks: 300,

            fan_in_count: baseline.fan_in_count.saturating_sub(2),
            fan_in_sum: baseline.fan_in_sum,

            fan_out_count: baseline.fan_out_count.saturating_sub(2),
            fan_out_sum: baseline.fan_out_sum,

            sg_count: baseline.sg_count,
            sg_sum: baseline.sg_sum,

            gs_count: baseline.gs_count,
            gs_sum: baseline.gs_sum,
        });

        //
        // 3. Stricter FI / FO
        //
        sweep.push(SweepConfig2 {
            label: "stricter_FI_FO",
            window_blocks: 300,

            fan_in_count: baseline.fan_in_count + 20,
            fan_in_sum: baseline.fan_in_sum,

            fan_out_count: baseline.fan_out_count + 20,
            fan_out_sum: baseline.fan_out_sum,

            sg_count: baseline.sg_count,
            sg_sum: baseline.sg_sum,

            gs_count: baseline.gs_count,
            gs_sum: baseline.gs_sum,
        });

        //
        // 4. Looser SG / GS
        //
        sweep.push(SweepConfig2 {
            label: "looser_SG_GS",
            window_blocks: 300,

            fan_in_count: baseline.fan_in_count,
            fan_in_sum: baseline.fan_in_sum,

            fan_out_count: baseline.fan_out_count,
            fan_out_sum: baseline.fan_out_sum,

            sg_count: baseline.sg_count.saturating_sub(1),
            sg_sum: baseline.sg_sum,

            gs_count: baseline.gs_count.saturating_sub(1),
            gs_sum: baseline.gs_sum,
        });

        //
        // 5. Stricter SG / GS
        //
        sweep.push(SweepConfig2 {
            label: "stricter_SG_GS",
            window_blocks: 300,

            fan_in_count: baseline.fan_in_count,
            fan_in_sum: baseline.fan_in_sum,

            fan_out_count: baseline.fan_out_count,
            fan_out_sum: baseline.fan_out_sum,

            sg_count: baseline.sg_count + 10,
            sg_sum: baseline.sg_sum,

            gs_count: baseline.gs_count + 10,
            gs_sum: baseline.gs_sum,
        });

        let mut results: Vec<DetectResult> = Vec::with_capacity(sweep.len());
        for cfg in &sweep {
            let res = run_detectability(&dataset, &groups, make_config_2(cfg));
            results.push(res);
        }

        print_detectability_table(&sweep, &results);

        // Sanity: baseline must be 4x 100% correct with 0 FP.
        let base_res = &results[0];
        assert_eq!(base_res.correct_fi, GROUPS_PER_MOTIF);
        assert_eq!(base_res.correct_fo, GROUPS_PER_MOTIF);
        assert_eq!(base_res.correct_sg, GROUPS_PER_MOTIF);
        assert_eq!(base_res.correct_gs, GROUPS_PER_MOTIF);
        assert_eq!(base_res.false_positives, 0);
    }


    #[test]
    fn partition_disjoint_txs_make_separate_buckets() {
        let d = AMLMotifDetector::new(cfg());

        let txs = vec![
            mk_tx(
                addr("0xa000000000000000000000000000000000000001"),
                addr("0xa000000000000000000000000000000000000002"),
                1,
            ),
            mk_tx(
                addr("0xa000000000000000000000000000000000000003"),
                addr("0xa000000000000000000000000000000000000004"),
                1,
            ),
            mk_tx(
                addr("0xa000000000000000000000000000000000000005"),
                addr("0xa000000000000000000000000000000000000006"),
                1,
            ),
        ];

        let buckets = d.partition_into_buckets(&txs);

        assert_eq!(buckets.len(), 3);
        assert_eq!(bucket_sizes(buckets), vec![1, 1, 1]);
    }

    #[test]
    fn partition_same_sender_txs_share_bucket() {
        let d = AMLMotifDetector::new(cfg());

        let src = addr("0xb000000000000000000000000000000000000001");

        let txs = vec![
            mk_tx(
                src,
                addr("0xb000000000000000000000000000000000000002"),
                1,
            ),
            mk_tx(
                src,
                addr("0xb000000000000000000000000000000000000003"),
                1,
            ),
            mk_tx(
                addr("0xb000000000000000000000000000000000000004"),
                addr("0xb000000000000000000000000000000000000005"),
                1,
            ),
        ];

        let buckets = d.partition_into_buckets(&txs);

        assert!(same_bucket(&buckets, 0, 1));
        assert!(!same_bucket(&buckets, 0, 2));
    }

    #[test]
    fn partition_same_receiver_txs_share_bucket() {
        let d = AMLMotifDetector::new(cfg());

        let sink = addr("0xc0000000000000000000000000000000000000ff");

        let txs = vec![
            mk_tx(
                addr("0xc000000000000000000000000000000000000001"),
                sink,
                1,
            ),
            mk_tx(
                addr("0xc000000000000000000000000000000000000002"),
                sink,
                1,
            ),
            mk_tx(
                addr("0xc000000000000000000000000000000000000003"),
                addr("0xc000000000000000000000000000000000000004"),
                1,
            ),
        ];

        let buckets = d.partition_into_buckets(&txs);

        assert!(same_bucket(&buckets, 0, 1));
        assert!(!same_bucket(&buckets, 0, 2));
    }

    #[test]
    fn partition_transitive_dependencies_collapse_component() {
        let d = AMLMotifDetector::new(cfg());

        let a = addr("0xd000000000000000000000000000000000000001");
        let b = addr("0xd000000000000000000000000000000000000002");
        let c = addr("0xd000000000000000000000000000000000000003");
        let e = addr("0xd000000000000000000000000000000000000004");

        let txs = vec![
            mk_tx(a, b, 1),
            mk_tx(b, c, 1),
            mk_tx(c, e, 1),
        ];

        let buckets = d.partition_into_buckets(&txs);

        assert_eq!(buckets.len(), 1);
        assert_eq!(buckets[0], vec![0, 1, 2]);
    }

    #[test]
    fn partition_sg_historical_intermediary_dependency_is_bucketed() {
        let mut d = AMLMotifDetector::new(cfg());

        let src = addr("0xe000000000000000000000000000000000000001");
        let inter = addr("0xe000000000000000000000000000000000000002");
        let sink = addr("0xe0000000000000000000000000000000000000ff");
        let other = addr("0xe000000000000000000000000000000000000003");

        // Historical edge: inter -> sink.
        // Then a candidate tx src -> inter can affect SG evaluation for a later
        // candidate tx other -> sink, even though src/other do not overlap directly.
        let history = vec![mk_tx(inter, sink, 5)];
        commit_history(&mut d, 10, &history);

        let txs = vec![
            mk_tx(src, inter, 5),
            mk_tx(other, sink, 5),
        ];

        let buckets = d.partition_into_buckets(&txs);

        assert!(
            same_bucket(&buckets, 0, 1),
            "candidate tx into historical SG intermediary must share bucket with tx into SG receiver"
        );
    }

    #[test]
    fn partition_hot_wallet_collapses_to_one_bucket() {
        let d = AMLMotifDetector::new(cfg());

        let hot = addr("0xf0000000000000000000000000000000000000aa");

        let txs = vec![
            mk_tx(hot, addr("0xf000000000000000000000000000000000000001"), 1),
            mk_tx(hot, addr("0xf000000000000000000000000000000000000002"), 1),
            mk_tx(hot, addr("0xf000000000000000000000000000000000000003"), 1),
            mk_tx(hot, addr("0xf000000000000000000000000000000000000004"), 1),
        ];

        let buckets = d.partition_into_buckets(&txs);

        assert_eq!(buckets.len(), 1);
        assert_eq!(buckets[0], vec![0, 1, 2, 3]);
    }

    #[test]
    fn parallel_matches_sequential_on_disjoint_clean_block() {
        let mut seq = AMLMotifDetector::new(cfg());
        let par = AMLMotifDetector::new(cfg());

        let txs = vec![
            mk_tx(
                addr("0x1100000000000000000000000000000000000001"),
                addr("0x1100000000000000000000000000000000000002"),
                1,
            ),
            mk_tx(
                addr("0x1100000000000000000000000000000000000003"),
                addr("0x1100000000000000000000000000000000000004"),
                1,
            ),
            mk_tx(
                addr("0x1100000000000000000000000000000000000005"),
                addr("0x1100000000000000000000000000000000000006"),
                1,
            ),
        ];

        let seq_rejected = seq.consensus_validate_block(&txs, 20, parent_hash(19));
        let par_rejected = par.consensus_validate_block_parallel_buckets(&txs, 20, parent_hash(19));

        assert_eq!(seq_rejected, par_rejected);
    }

    #[test]
    fn parallel_matches_sequential_on_fan_out_block() {
        let mut seq = AMLMotifDetector::new(cfg());
        let par = AMLMotifDetector::new(cfg());

        let src = addr("0x2200000000000000000000000000000000000001");

        let txs = vec![
            mk_tx(src, addr("0x2200000000000000000000000000000000000002"), 6),
            mk_tx(src, addr("0x2200000000000000000000000000000000000003"), 6),
            mk_tx(src, addr("0x2200000000000000000000000000000000000004"), 1),
        ];

        let seq_rejected = seq.consensus_validate_block(&txs, 20, parent_hash(19));
        let par_rejected = par.consensus_validate_block_parallel_buckets(&txs, 20, parent_hash(19));

        assert_eq!(seq_rejected, par_rejected);
    }

    #[test]
    fn parallel_matches_sequential_on_fan_in_block() {
        let mut seq = AMLMotifDetector::new(cfg());
        let par = AMLMotifDetector::new(cfg());

        let sink = addr("0x33000000000000000000000000000000000000ff");

        let txs = vec![
            mk_tx(addr("0x3300000000000000000000000000000000000001"), sink, 5),
            mk_tx(addr("0x3300000000000000000000000000000000000002"), sink, 5),
            mk_tx(addr("0x3300000000000000000000000000000000000003"), sink, 1),
        ];

        let seq_rejected = seq.consensus_validate_block(&txs, 20, parent_hash(19));
        let par_rejected = par.consensus_validate_block_parallel_buckets(&txs, 20, parent_hash(19));

        assert_eq!(seq_rejected, par_rejected);
    }

    #[test]
    fn parallel_matches_sequential_on_scatter_gather_candidate_block() {
        let mut seq = AMLMotifDetector::new(cfg());
        let par = AMLMotifDetector::new(cfg());

        let source = addr("0x4400000000000000000000000000000000000001");
        let i1 = addr("0x4400000000000000000000000000000000000002");
        let i2 = addr("0x4400000000000000000000000000000000000003");
        let i3 = addr("0x4400000000000000000000000000000000000004");
        let i4 = addr("0x4400000000000000000000000000000000000005");
        let sink = addr("0x44000000000000000000000000000000000000ff");

        // Need > scatter_gather_count_threshold, and cfg threshold is 3,
        // so use 4 intermediaries.
        let txs = vec![
            mk_tx(source, i1, 3),
            mk_tx(i1, sink, 3),
            mk_tx(source, i2, 3),
            mk_tx(i2, sink, 3),
            mk_tx(source, i3, 3),
            mk_tx(i3, sink, 3),
            mk_tx(source, i4, 3),
            mk_tx(i4, sink, 3),
        ];

        let seq_rejected = seq.consensus_validate_block(&txs, 20, parent_hash(19));
        let par_rejected = par.consensus_validate_block_parallel_buckets(&txs, 20, parent_hash(19));

        assert_eq!(seq_rejected, par_rejected);
    }

    #[test]
    fn parallel_matches_sequential_on_gather_scatter_candidate_block() {
        let mut seq = AMLMotifDetector::new(cfg());
        let par = AMLMotifDetector::new(cfg());

        let s1 = addr("0x5500000000000000000000000000000000000001");
        let s2 = addr("0x5500000000000000000000000000000000000002");
        let s3 = addr("0x5500000000000000000000000000000000000003");
        let s4 = addr("0x5500000000000000000000000000000000000004");
        let hub = addr("0x55000000000000000000000000000000000000aa");
        let r1 = addr("0x55000000000000000000000000000000000000bb");
        let r2 = addr("0x55000000000000000000000000000000000000bc");
        let r3 = addr("0x55000000000000000000000000000000000000bd");
        let r4 = addr("0x55000000000000000000000000000000000000be");

        // Need sources_len > 3 and fan_out_count > 3.
        let txs = vec![
            mk_tx(s1, hub, 3),
            mk_tx(s2, hub, 3),
            mk_tx(s3, hub, 3),
            mk_tx(s4, hub, 3),
            mk_tx(hub, r1, 3),
            mk_tx(hub, r2, 3),
            mk_tx(hub, r3, 3),
            mk_tx(hub, r4, 3),
        ];

        let seq_rejected = seq.consensus_validate_block(&txs, 20, parent_hash(19));
        let par_rejected = par.consensus_validate_block_parallel_buckets(&txs, 20, parent_hash(19));

        assert_eq!(seq_rejected, par_rejected);
    }

    #[test]
    fn parallel_matches_sequential_with_historical_sg_intermediary() {
        let mut seq = AMLMotifDetector::new(cfg());
        let mut par = AMLMotifDetector::new(cfg());

        let source = addr("0x6600000000000000000000000000000000000001");
        let i1 = addr("0x6600000000000000000000000000000000000002");
        let i2 = addr("0x6600000000000000000000000000000000000003");
        let i3 = addr("0x6600000000000000000000000000000000000004");
        let i4 = addr("0x6600000000000000000000000000000000000005");
        let sink = addr("0x66000000000000000000000000000000000000ff");

        let history = vec![
            mk_tx(i1, sink, 3),
            mk_tx(i2, sink, 3),
            mk_tx(i3, sink, 3),
            mk_tx(i4, sink, 3),
        ];

        commit_history(&mut seq, 18, &history);
        commit_history(&mut par, 18, &history);

        let txs = vec![
            mk_tx(source, i1, 3),
            mk_tx(source, i2, 3),
            mk_tx(source, i3, 3),
            mk_tx(source, i4, 3),
            mk_tx(addr("0x6600000000000000000000000000000000000006"), sink, 1),
        ];

        let seq_rejected = seq.consensus_validate_block(&txs, 20, parent_hash(19));
        let par_rejected = par.consensus_validate_block_parallel_buckets(&txs, 20, parent_hash(19));

        assert_eq!(seq_rejected, par_rejected);
    }

    #[test]
    fn synthetic_dataset_bucketing_only_timing() {
        use std::collections::BTreeMap;
        use std::time::Instant;

        let (dataset, _groups) = build_dataset();

        // Group synthetic txs by block, preserving block order.
        let mut by_block: BTreeMap<u64, Vec<(Address, Address, Address, U256)>> = BTreeMap::new();

        for tx in dataset.iter() {
            by_block
                .entry(tx.block)
                .or_default()
                .push((tx.token, tx.from, tx.to, tx.amount));
        }

        let mut detector = AMLMotifDetector::new(cfg());

        let mut total_ns = 0u128;
        let mut total_txs = 0usize;
        let mut total_blocks = 0usize;
        let mut total_buckets = 0usize;
        let mut max_bucket_size = 0usize;
        let mut max_block_txs = 0usize;

        for (block, txs) in by_block.iter() {
            if txs.is_empty() {
                continue;
            }

            let t0 = Instant::now();
            let buckets = detector.partition_into_buckets(txs);
            total_ns += t0.elapsed().as_nanos();

            total_blocks += 1;
            total_txs += txs.len();
            total_buckets += buckets.len();
            max_block_txs = max_block_txs.max(txs.len());

            if let Some(local_max) = buckets.iter().map(|b| b.len()).max() {
                max_bucket_size = max_bucket_size.max(local_max);
            }

            // Important: this is bucketing-only timing, so we commit all txs just to
            // let the graph evolve across blocks. This does NOT measure AML filtering.
            detector.block_commit(*block, parent_hash(block.saturating_sub(1)), txs);
        }

        let avg_bucket_time_us = if total_blocks == 0 {
            0.0
        } else {
            total_ns as f64 / total_blocks as f64 / 1_000.0
        };

        let avg_txs_per_block = if total_blocks == 0 {
            0.0
        } else {
            total_txs as f64 / total_blocks as f64
        };

        let avg_buckets_per_block = if total_blocks == 0 {
            0.0
        } else {
            total_buckets as f64 / total_blocks as f64
        };

        let avg_bucket_size = if total_buckets == 0 {
            0.0
        } else {
            total_txs as f64 / total_buckets as f64
        };

        println!();
        println!("================ Bucketing-only timing ================");
        println!("blocks:                    {}", total_blocks);
        println!("txs:                       {}", total_txs);
        println!("max txs/block:             {}", max_block_txs);
        println!("total buckets:             {}", total_buckets);
        println!("max bucket size:           {}", max_bucket_size);
        println!("avg txs/block:             {:.2}", avg_txs_per_block);
        println!("avg buckets/block:         {:.2}", avg_buckets_per_block);
        println!("avg bucket size:           {:.2}", avg_bucket_size);
        println!("avg bucketing time/block:  {:.3} us", avg_bucket_time_us);
        println!("total bucketing time:      {:.3} ms", total_ns as f64 / 1_000_000.0);
        println!("=======================================================");
        println!();

        assert!(total_blocks > 0);
    }
}

