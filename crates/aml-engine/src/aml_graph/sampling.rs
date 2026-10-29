//! Uniform bounded AML witness discovery for AMLMotifDetector.
//!
//! Place this code in the same Rust module as AMLMotifDetector so it can reuse
//! private helpers such as neighbors_to_vec_with_ephemeral and window_sum_full.
//! It does not replace the existing exact checks.

use super::{
    AMLMotifDetector,
    Config,
    TransferEdge,
};

use petgraph::Direction::{Incoming, Outgoing};
use alloy_primitives::{keccak256, Address, B256, U256};
use std::collections::BinaryHeap;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum SampledMotifKind {
    FanOut = 1,
    GatherScatter = 2,
    FanIn = 3,
    ScatterGather = 4,
}

#[derive(Clone, Debug)]
pub struct SamplingConfig {
    pub fan_in_budget: usize,
    pub fan_out_budget: usize,
    /// Additional incoming pair-evaluation budget; outgoing values reuse Fan-Out.
    pub gather_scatter_budget: usize,
    /// Additional SG pair-evaluation budget (excluding reused Fan-In results).
    pub scatter_gather_budget: usize,
    pub validator_id: B256,
    pub randomness: B256,
}

#[derive(Clone, Debug)]
pub struct SamplingContext {
    pub block_hash: B256,
    pub block_number: u64,
    pub tx_index: usize,
}

#[derive(Clone, Debug, Default)]
pub struct SamplingMetrics {
    /// Neighbor identities examined while selecting bounded samples (not all stored).
    pub candidate_count: u64,
    /// Number of candidates selected/visited from sampled orders.
    pub sampled_candidates: u64,
    /// Number of pair-aggregate evaluations (including temporally cut off SG).
    pub pair_sum_evaluations: u64,
    /// Number of complete x->m->r candidates evaluated by SG.
    pub sg_branch_evaluations: u64,
}

impl SamplingMetrics {
    fn merge(&mut self, rhs: &Self) {
        self.candidate_count += rhs.candidate_count;
        self.sampled_candidates += rhs.sampled_candidates;
        self.pair_sum_evaluations += rhs.pair_sum_evaluations;
        self.sg_branch_evaluations += rhs.sg_branch_evaluations;
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetTxEvidence {
    pub tx_index: usize,
    pub token: Address,
    pub block_hash: B256,
    pub from: Address,
    pub to: Address,
    pub amount: U256,
    pub block: u64,
}

#[derive(Clone, Debug)]
pub struct PairEvidence {
    pub from: Address,
    pub to: Address,
    /// Discovery-time aggregate. Verification recomputes this value.
    pub amount: U256,
    /// Discovery-time latest contributing block. Verification recomputes it.
    pub max_block: u64,
}

#[derive(Clone, Debug)]
pub struct FanWitness {
    pub target: TargetTxEvidence,
    pub kind: SampledMotifKind,
    pub center: Address,
    pub pairs: Vec<PairEvidence>,
}

#[derive(Clone, Debug)]
pub struct GatherScatterWitness {
    pub target: TargetTxEvidence,
    pub hub: Address,
    pub incoming: Vec<PairEvidence>,
    pub outgoing: Vec<PairEvidence>,
}

#[derive(Clone, Debug)]
pub struct ScatterGatherBranchEvidence {
    pub source: Address,
    pub intermediary: Address,
    pub receiver: Address,
    pub source_to_intermediary: PairEvidence,
    pub intermediary_to_receiver: PairEvidence,
}

#[derive(Clone, Debug)]
pub struct ScatterGatherWitness {
    pub target: TargetTxEvidence,
    pub source: Address,
    pub receiver: Address,
    pub branches: Vec<ScatterGatherBranchEvidence>,
}

#[derive(Clone, Debug)]
pub enum AMLWitness {
    FanIn(FanWitness),
    FanOut(FanWitness),
    GatherScatter(GatherScatterWitness),
    ScatterGather(ScatterGatherWitness),
}

#[derive(Clone, Debug)]
pub struct DiscoveredWitness {
    pub witness: AMLWitness,
    pub metrics: SamplingMetrics,
}

#[derive(Clone, Debug, Default)]
pub struct SampledCheckResult {
    /// Independent discovery can return more than one motif witness.
    pub witnesses: Vec<DiscoveredWitness>,
    pub total_metrics: SamplingMetrics,
}

impl SampledCheckResult {
    pub fn found_any(&self) -> bool {
        !self.witnesses.is_empty()
    }
}

/// Domain-separated keccak-based seed. `randomness` must be fixed by an
/// externally specified protocol before the candidate can be sampled; this
/// hash alone is not a source of unpredictability.
fn derive_sampling_seed(
    cfg: &SamplingConfig,
    ctx: &SamplingContext,
    kind: SampledMotifKind,
    lane: u8,
) -> B256 {
    let mut bytes = Vec::with_capacity(17 + 32 * 3 + 8 * 2 + 2);
    bytes.extend_from_slice(b"AML-SAMPLE-v1");
    bytes.extend_from_slice(cfg.randomness.as_slice());
    bytes.extend_from_slice(cfg.validator_id.as_slice());
    bytes.extend_from_slice(ctx.block_hash.as_slice());
    bytes.extend_from_slice(&ctx.block_number.to_le_bytes());
    bytes.extend_from_slice(&(ctx.tx_index as u64).to_le_bytes());
    bytes.push(kind as u8);
    bytes.push(lane);
    keccak256(bytes)
}

fn derive_sampling_seed_for_address(
    sampling: &SamplingConfig,
    context: &SamplingContext,
    kind: SampledMotifKind,
    lane: u8,
    address: Address,
) -> B256 {
    let seed = derive_sampling_seed(sampling, context, kind, lane);
    let mut bytes = Vec::with_capacity(32 + 20);
    bytes.extend_from_slice(seed.as_slice());
    bytes.extend_from_slice(address.as_slice());
    keccak256(bytes)
}

/// Keep the k lowest keccak priorities without replacement.
/// Cost is O(d log(k+1)) time / O(k) extra space for degree d, rather than
/// materializing and sorting all d candidate addresses. The same seed and
/// population give the same sample, independent of hash-set iteration order;
/// increasing k preserves the previous prefix.
fn keep_priority(
    heap: &mut BinaryHeap<(B256, Address)>,
    seed: B256,
    address: Address,
    budget: usize,
) {
    if budget == 0 { return; }
    let mut bytes = [0u8; 52];
    bytes[..32].copy_from_slice(seed.as_slice());
    bytes[32..].copy_from_slice(address.as_slice());
    let priority = keccak256(bytes);
    let item = (priority, address);
    if heap.len() < budget {
        heap.push(item);
    } else if heap.peek().is_some_and(|largest| item < *largest) {
        heap.pop();
        heap.push(item);
    }
}

impl AMLMotifDetector {
    /// Sample a neighborhood without first copying / sorting all neighbors.
    /// Returns (sample ordered by priority, unique population count).
    fn sampled_neighbors(
        &mut self,
        address: Address,
        direction: petgraph::Direction,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
        budget: usize,
        seed: B256,
    ) -> (Vec<Address>, usize) {
        self.ensure_neighbors_cached(address, direction);
        let cached = self.get_neighbors_cached(address, direction);
        let mut heap = BinaryHeap::new();
        for &neighbor in cached {
            keep_priority(&mut heap, seed, neighbor, budget);
        }
        let mut count = cached.len();
        if let Some((from, to, _)) = ephemeral {
            let neighbor = match direction {
                Incoming if to == address => Some(from),
                Outgoing if from == address => Some(to),
                _ => None,
            };
            if let Some(other) = neighbor {
                if !cached.contains(&other) {
                    count += 1;
                    keep_priority(&mut heap, seed, other, budget);
                }
            }
        }
        (heap.into_sorted_vec().into_iter().map(|(_, a)| a).collect(), count)
    }

    /// Sum eligible source->intermediary transfers with the *original* rolling
    /// window lower bound and the SG latest-intermediary->receiver cutoff.
    /// Pair-scoped: avoids scanning every source, unlike the exact detector's
    /// one-pass `sg_left_by_source` helper.
    fn sampled_sg_pair_through(
        &self,
        source: Address,
        intermediary: Address,
        current_block: u64,
        cutoff: u64,
    ) -> (U256, u64) {
        let in_scope = |h: u64| {
            h <= cutoff && current_block >= h
                && current_block - h < self.config.window_blocks
        };
        let mut sum = U256::ZERO;
        let mut max_block = 0u64;
        if let (Some(&a), Some(&b)) =
            (self.node_map.get(&source), self.node_map.get(&intermediary))
        {
            for edge in self.graph.edges_connecting(a, b) {
                let transfer = edge.weight();
                if in_scope(transfer.block) {
                    sum += transfer.amount;
                    max_block = max_block.max(transfer.block);
                }
            }
        }
        for (from, transfer) in self.overlay.incoming_slice(&intermediary) {
            if *from == source && in_scope(transfer.block) {
                sum += transfer.amount;
                max_block = max_block.max(transfer.block);
            }
        }
        // No ephemeral first-hop edge: as in the exact receiver-centric SG
        // check, the candidate is the intermediary->receiver edge.
        (sum, max_block)
    }


    pub(super) fn sampled_check_tx_all_motifs(
        &mut self,
        token: Address,
        from: Address,
        to: Address,
        amount: U256,
        block: u64,
        sampling: &SamplingConfig,
        context: &SamplingContext,
    ) -> SampledCheckResult {
        let candidate_edge = TransferEdge { amount, block };
        let ephemeral = Some((from, to, &candidate_edge));
        assert_eq!(block, context.block_number, "sampling context block mismatch");
        let target = TargetTxEvidence {
            tx_index: context.tx_index,
            token,
            block_hash: context.block_hash,
            from,
            to,
            amount,
            block,
        };

        let sender_result = self.sampled_check_from_view_ephemeral(
            &target,
            ephemeral,
            sampling,
            context,
        );
        if sender_result.found_any() {
            return sender_result;
        }

        let receiver_result = self.sampled_check_against_view_ephemeral(
            &target,
            ephemeral,
            sampling,
            context,
        );

        let mut combined = sender_result;
        combined.total_metrics.merge(&receiver_result.total_metrics);
        combined.witnesses.extend(receiver_result.witnesses);
        combined
    }

    /// Sender-side shared path. The outgoing sample is evaluated once.
    ///
    /// Budget semantics:
    /// - fan_out_budget caps shared outgoing pair evaluations.
    /// - gather_scatter_budget caps additional incoming pair evaluations.
    fn sampled_check_from_view_ephemeral(
        &mut self,
        target: &TargetTxEvidence,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
        sampling: &SamplingConfig,
        context: &SamplingContext,
    ) -> SampledCheckResult {
        let mut result = SampledCheckResult::default();
        let mut metrics = SamplingMetrics::default();

        // GS reuses Fan-Out's outgoing evidence. Without an outgoing sample,
        // neither sender-side motif can produce a witness.
        if sampling.fan_out_budget == 0 {
            return result;
        }

        // One canonical outgoing sample is shared by Fan-Out and GS.
        let (destinations, candidate_count) = self.sampled_neighbors(
            target.from, Outgoing, ephemeral, sampling.fan_out_budget,
            derive_sampling_seed(sampling, context, SampledMotifKind::FanOut, 0),
        );
        metrics.candidate_count += candidate_count as u64;
        let outgoing_k = destinations.len();

        let mut outgoing_count = 0u64;
        let mut outgoing_sum = U256::ZERO;
        let mut outgoing_evidence = Vec::with_capacity(outgoing_k);

        for &receiver in destinations.iter().take(outgoing_k) {
            metrics.sampled_candidates += 1;
            metrics.pair_sum_evaluations += 1;

            let (pair_amount, max_block) = self.window_sum_full(
                target.from,
                receiver,
                target.block,
                ephemeral,
            );
            if pair_amount == U256::ZERO {
                continue;
            }

            outgoing_count += 1;
            outgoing_sum += pair_amount;
            outgoing_evidence.push(PairEvidence {
                from: target.from,
                to: receiver,
                amount: pair_amount,
                max_block,
            });

            if outgoing_count > self.config.fan_out_count_threshold
                || outgoing_sum > self.config.fan_out_sum_threshold
            {
                let witness = AMLWitness::FanOut(FanWitness {
                    target: target.clone(),
                    kind: SampledMotifKind::FanOut,
                    center: target.from,
                    pairs: outgoing_evidence,
                });
                result.total_metrics.merge(&metrics);
                result.witnesses.push(DiscoveredWitness {
                    witness,
                    metrics,
                });
                return result;
            }
        }

        if sampling.gather_scatter_budget == 0 {
            result.total_metrics.merge(&metrics);
            return result;
        }

        // Fan-Out did not trigger. GS reuses the exact outgoing sample results
        // above and spends only its additional incoming budget.
        let (sources, candidate_count) = self.sampled_neighbors(
            target.from, Incoming, ephemeral, sampling.gather_scatter_budget,
            derive_sampling_seed(sampling, context, SampledMotifKind::GatherScatter, 1),
        );
        metrics.candidate_count += candidate_count as u64;
        let incoming_k = sources.len();

        let mut incoming_count = 0u64;
        let mut incoming_sum = U256::ZERO;
        let mut incoming_evidence = Vec::with_capacity(incoming_k);

        for &source in sources.iter().take(incoming_k) {
            metrics.sampled_candidates += 1;
            metrics.pair_sum_evaluations += 1;

            let (pair_amount, max_block) = self.window_sum_full(
                source,
                target.from,
                target.block,
                ephemeral,
            );
            if pair_amount == U256::ZERO {
                continue;
            }

            incoming_count += 1;
            incoming_sum += pair_amount;
            incoming_evidence.push(PairEvidence {
                from: source,
                to: target.from,
                amount: pair_amount,
                max_block,
            });

            if incoming_count > self.config.gather_scatter_count_threshold
                && outgoing_count > self.config.gather_scatter_count_threshold
                && incoming_sum.min(outgoing_sum)
                > self.config.gather_scatter_threshold
            {
                let witness = AMLWitness::GatherScatter(
                    GatherScatterWitness {
                        target: target.clone(),
                        hub: target.from,
                        incoming: incoming_evidence,
                        outgoing: outgoing_evidence,
                    },
                );
                result.total_metrics.merge(&metrics);
                result.witnesses.push(DiscoveredWitness {
                    witness,
                    metrics,
                });
                return result;
            }
        }

        result.total_metrics.merge(&metrics);
        result
    }

    /// Receiver-side shared path. Fan-In and SG share the same independently
    /// seeded incoming-neighbor order; SG reuses Fan-In's pair aggregates.
    /// SG schedules sampled source pairs round-robin across intermediaries.
    /// The SG budget applies to extra right-side lookups and selected left-side
    /// pair aggregates; reuse from Fan-In does not cost another evaluation.
    fn sampled_check_against_view_ephemeral(
        &mut self,
        target: &TargetTxEvidence,
        ephemeral: Option<(Address, Address, &TransferEdge)>,
        sampling: &SamplingConfig,
        context: &SamplingContext,
    ) -> SampledCheckResult {
        let mut result = SampledCheckResult::default();
        let mut metrics = SamplingMetrics::default();
        if sampling.fan_in_budget == 0 && sampling.scatter_gather_budget == 0 {
            return result;
        }

        let requested_prefix = sampling.fan_in_budget.max(sampling.scatter_gather_budget);
        let (intermediaries, candidates) = self.sampled_neighbors(
            target.to, Incoming, ephemeral, requested_prefix,
            derive_sampling_seed(sampling, context, SampledMotifKind::FanIn, 0),
        );
        metrics.candidate_count += candidates as u64;
        let fan_in_k = sampling.fan_in_budget.min(intermediaries.len());
        let mut fan_in_count = 0u64;
        let mut fan_in_sum = U256::ZERO;
        let mut fan_in_evidence = Vec::with_capacity(fan_in_k);
        let mut evaluated_right: FxHashMap<Address, (U256, u64)> = FxHashMap::default();

        for &source in intermediaries.iter().take(fan_in_k) {
            metrics.sampled_candidates += 1;
            metrics.pair_sum_evaluations += 1;
            let pair = self.window_sum_full(source, target.to, target.block, ephemeral);
            evaluated_right.insert(source, pair);
            if pair.0 == U256::ZERO { continue; }
            fan_in_count += 1;
            fan_in_sum += pair.0;
            fan_in_evidence.push(PairEvidence {
                from: source, to: target.to, amount: pair.0, max_block: pair.1,
            });
            if fan_in_count > self.config.fan_in_count_threshold
                || fan_in_sum > self.config.fan_in_sum_threshold
            {
                let witness = AMLWitness::FanIn(FanWitness {
                    target: target.clone(), kind: SampledMotifKind::FanIn,
                    center: target.to, pairs: fan_in_evidence,
                });
                result.total_metrics.merge(&metrics);
                result.witnesses.push(DiscoveredWitness { witness, metrics });
                return result;
            }
        }
        if sampling.scatter_gather_budget == 0 {
            result.total_metrics.merge(&metrics);
            return result;
        }

        struct SgLane {
            intermediary: Address,
            right_amount: U256,
            right_max_block: u64,
            sources: Vec<Address>,
            cursor: usize,
        }

        let mut sg_budget_used = 0usize;
        let mut source_state: FxHashMap<
            Address, (u64, U256, Vec<ScatterGatherBranchEvidence>)
        > = FxHashMap::default();
        let mut next_intermediary = 0usize;
        // Open enough intermediaries to allow the count threshold to trigger,
        // then spend remaining evaluations in balanced rounds. If a batch is
        // exhausted and budget remains, we open more intermediaries.
        let batch_size = ((sampling.scatter_gather_budget + 1) / 2)
            .max((self.config.scatter_gather_count_threshold as usize).saturating_add(1))
            .max(1);

        while sg_budget_used < sampling.scatter_gather_budget {
            let mut lanes: Vec<SgLane> = Vec::new();
            while next_intermediary < intermediaries.len() && lanes.len() < batch_size {
                let intermediary = intermediaries[next_intermediary];
                next_intermediary += 1;
                let (right_amount, right_max_block) =
                    if let Some(&pair) = evaluated_right.get(&intermediary) {
                        pair
                    } else {
                        if sg_budget_used >= sampling.scatter_gather_budget { break; }
                        sg_budget_used += 1;
                        metrics.sampled_candidates += 1;
                        metrics.pair_sum_evaluations += 1;
                        let pair = self.window_sum_full(
                            intermediary, target.to, target.block, ephemeral
                        );
                        evaluated_right.insert(intermediary, pair);
                        pair
                    };
                if right_amount == U256::ZERO { continue; }

                // A single intermediary may offer many sources, but each one
                // receives just one pair evaluation per round.
                let (sources, candidate_count) = self.sampled_neighbors(
                    intermediary, Incoming, None, sampling.scatter_gather_budget,
                    derive_sampling_seed_for_address(
                        sampling, context, SampledMotifKind::ScatterGather,
                        1, intermediary,
                    ),
                );
                metrics.candidate_count += candidate_count as u64;
                if sources.is_empty() { continue; }
                lanes.push(SgLane {
                    intermediary, right_amount, right_max_block,
                    sources, cursor: 0,
                });
            }
            if lanes.is_empty() {
                if next_intermediary >= intermediaries.len() { break; }
                continue;
            }

            loop {
                let mut progressed = false;
                for lane in &mut lanes {
                    if sg_budget_used >= sampling.scatter_gather_budget { break; }
                    if lane.cursor >= lane.sources.len() { continue; }
                    let source = lane.sources[lane.cursor];
                    lane.cursor += 1;
                    progressed = true;
                    sg_budget_used += 1;
                    metrics.sampled_candidates += 1;
                    metrics.pair_sum_evaluations += 1;
                    metrics.sg_branch_evaluations += 1;

                    let (left_amount, left_max_block) = self.sampled_sg_pair_through(
                        source, lane.intermediary, target.block, lane.right_max_block
                    );
                    if left_amount == U256::ZERO { continue; }
                    let branch = ScatterGatherBranchEvidence {
                        source, intermediary: lane.intermediary, receiver: target.to,
                        source_to_intermediary: PairEvidence {
                            from: source, to: lane.intermediary,
                            amount: left_amount, max_block: left_max_block,
                        },
                        intermediary_to_receiver: PairEvidence {
                            from: lane.intermediary, to: target.to,
                            amount: lane.right_amount, max_block: lane.right_max_block,
                        },
                    };
                    let state = source_state.entry(source)
                        .or_insert_with(|| (0, U256::ZERO, Vec::new()));
                    state.0 += 1;
                    state.1 += left_amount.min(lane.right_amount);
                    state.2.push(branch);
                    if state.0 > self.config.scatter_gather_count_threshold
                        && state.1 > self.config.scatter_gather_threshold
                    {
                        let witness = AMLWitness::ScatterGather(ScatterGatherWitness {
                            target: target.clone(), source, receiver: target.to,
                            branches: state.2.clone(),
                        });
                        result.total_metrics.merge(&metrics);
                        result.witnesses.push(DiscoveredWitness { witness, metrics });
                        return result;
                    }
                }
                if !progressed || sg_budget_used >= sampling.scatter_gather_budget { break; }
            }
            if next_intermediary >= intermediaries.len() { break; }
        }
        result.total_metrics.merge(&metrics);
        result
    }

    /// Public verification requires binding the claim to an independently
    /// authenticated transaction in the proposed block. Caller must arrange the
    /// *same committed + accepted-prefix overlay* as discovery before calling.
    /// Caller must derive `expected` from the actual block contents, not from
    /// untrusted witness fields. `block_hash` binds block context but does not
    /// prove a shared graph/overlay state. Witness dissemination and voting
    /// remain outside this module.
    pub fn verify_aml_witness_for_tx(
        &mut self,
        witness: &AMLWitness,
        expected: &TargetTxEvidence,
    ) -> bool {
        let claimed = match witness {
            AMLWitness::FanIn(w) | AMLWitness::FanOut(w) => &w.target,
            AMLWitness::GatherScatter(w) => &w.target,
            AMLWitness::ScatterGather(w) => &w.target,
        };
        claimed == expected && self.verify_aml_witness(witness)
    }

    /// Recompute evidence against committed graph + accepted prefix + candidate.
    /// Internal only: it does not authenticate the referenced transaction.
    fn verify_aml_witness(&mut self, witness: &AMLWitness) -> bool {
        match witness {
            AMLWitness::FanIn(w) => self.verify_fan_witness(w, true),
            AMLWitness::FanOut(w) => self.verify_fan_witness(w, false),
            AMLWitness::GatherScatter(w) => self.verify_gs_witness(w),
            AMLWitness::ScatterGather(w) => self.verify_sg_witness(w),
        }
    }

    fn verify_fan_witness(&mut self, witness: &FanWitness, incoming: bool) -> bool {
        if (incoming && (witness.kind != SampledMotifKind::FanIn
            || witness.center != witness.target.to))
            || (!incoming && (witness.kind != SampledMotifKind::FanOut
            || witness.center != witness.target.from))
        { return false; }
        let edge = TransferEdge {
            amount: witness.target.amount,
            block: witness.target.block,
        };
        let ephemeral = Some((witness.target.from, witness.target.to, &edge));
        let mut seen = rustc_hash::FxHashSet::default();
        let mut count = 0u64;
        let mut sum = U256::ZERO;
        for pair in &witness.pairs {
            let counterparty = if incoming { pair.from } else { pair.to };
            if !seen.insert(counterparty) {
                return false;
            }
            if incoming && pair.to != witness.center {
                return false;
            }
            if !incoming && pair.from != witness.center {
                return false;
            }
            let (amount, max_block) = self.window_sum_full(
                pair.from,
                pair.to,
                witness.target.block,
                ephemeral,
            );
            if amount == U256::ZERO || amount != pair.amount || max_block != pair.max_block {
                return false;
            }
            count += 1;
            sum += amount;
        }
        if incoming {
            count > self.config.fan_in_count_threshold
                || sum > self.config.fan_in_sum_threshold
        } else {
            count > self.config.fan_out_count_threshold
                || sum > self.config.fan_out_sum_threshold
        }
    }

    fn verify_gs_witness(&mut self, witness: &GatherScatterWitness) -> bool {
        if witness.hub != witness.target.from { return false; }
        let edge = TransferEdge {
            amount: witness.target.amount,
            block: witness.target.block,
        };
        let ephemeral = Some((witness.target.from, witness.target.to, &edge));
        let mut in_seen = rustc_hash::FxHashSet::default();
        let mut out_seen = rustc_hash::FxHashSet::default();
        let mut incoming_sum = U256::ZERO;
        let mut outgoing_sum = U256::ZERO;

        for pair in &witness.incoming {
            if pair.to != witness.hub || !in_seen.insert(pair.from) {
                return false;
            }
            let (amount, max_block) = self.window_sum_full(
                pair.from,
                pair.to,
                witness.target.block,
                ephemeral,
            );
            if amount == U256::ZERO || amount != pair.amount || max_block != pair.max_block {
                return false;
            }
            incoming_sum += amount;
        }
        for pair in &witness.outgoing {
            if pair.from != witness.hub || !out_seen.insert(pair.to) {
                return false;
            }
            let (amount, max_block) = self.window_sum_full(
                pair.from,
                pair.to,
                witness.target.block,
                ephemeral,
            );
            if amount == U256::ZERO || amount != pair.amount || max_block != pair.max_block {
                return false;
            }
            outgoing_sum += amount;
        }

        in_seen.len() as u64 > self.config.gather_scatter_count_threshold
            && out_seen.len() as u64 > self.config.gather_scatter_count_threshold
            && incoming_sum.min(outgoing_sum) > self.config.gather_scatter_threshold
    }

    fn verify_sg_witness(&mut self, witness: &ScatterGatherWitness) -> bool {
        if witness.receiver != witness.target.to { return false; }
        let edge = TransferEdge {
            amount: witness.target.amount,
            block: witness.target.block,
        };
        let ephemeral = Some((witness.target.from, witness.target.to, &edge));
        let mut seen = FxHashSet::default();
        let mut total_flow = U256::ZERO;

        for branch in &witness.branches {
            if branch.source != witness.source
                || branch.receiver != witness.receiver
                || !seen.insert(branch.intermediary)
                || branch.source_to_intermediary.from != branch.source
                || branch.source_to_intermediary.to != branch.intermediary
                || branch.intermediary_to_receiver.from != branch.intermediary
                || branch.intermediary_to_receiver.to != branch.receiver
            { return false; }
            let (right_amount, right_max_block) = self.window_sum_full(
                branch.intermediary, branch.receiver, witness.target.block,
                ephemeral,
            );
            let (left_amount, left_max_block) = self.sampled_sg_pair_through(
                branch.source, branch.intermediary, witness.target.block,
                right_max_block,
            );
            if left_amount == U256::ZERO
                || right_amount == U256::ZERO
                || left_amount != branch.source_to_intermediary.amount
                || left_max_block != branch.source_to_intermediary.max_block
                || right_amount != branch.intermediary_to_receiver.amount
                || right_max_block != branch.intermediary_to_receiver.max_block
            { return false; }
            total_flow += left_amount.min(right_amount);
        }
        seen.len() as u64 > self.config.scatter_gather_count_threshold
            && total_flow > self.config.scatter_gather_threshold
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::Config;
    use std::collections::HashSet;

    fn addr(n: u8) -> Address { Address::from([n; 20]) }
    fn hash(n: u8) -> B256 { B256::from([n; 32]) }
    fn val(n: u64) -> U256 { U256::from(n) }
    fn config() -> Config {
        Config {
            window_blocks: 20,
            fan_in_count_threshold: 100,
            fan_in_sum_threshold: val(100_000),
            fan_out_count_threshold: 100,
            fan_out_sum_threshold: val(100_000),
            gather_scatter_count_threshold: 100,
            gather_scatter_threshold: val(100_000),
            scatter_gather_count_threshold: 3,
            scatter_gather_threshold: val(350),
        }
    }
    fn sampling(budget: usize) -> SamplingConfig {
        SamplingConfig {
            fan_in_budget: 0, fan_out_budget: 0,
            gather_scatter_budget: 0, scatter_gather_budget: budget,
            validator_id: hash(0xa1), randomness: hash(0x42),
        }
    }
    fn context() -> SamplingContext {
        SamplingContext { block_hash: hash(0x88), block_number: 11, tx_index: 0 }
    }
    fn commit(d: &mut AMLMotifDetector, block: u64, edges: &[(Address, Address, U256)]) {
        let txs: Vec<_> = edges.iter().map(|&(a, b, amount)|
            (addr(0xf0), a, b, amount)).collect();
        d.block_commit(block, B256::ZERO, &txs);
    }
    fn sg_fixture(with_late_transfers: bool) -> AMLMotifDetector {
        let mut d = AMLMotifDetector::new(config());
        let s = addr(0x50);
        let receiver = addr(0x90);
        let intermediaries = [addr(21), addr(22), addr(23), addr(24)];
        let first: Vec<_> = intermediaries.iter().map(|&m| (s, m, val(100))).collect();
        commit(&mut d, 8, &first);
        let forwarded: Vec<_> = intermediaries[..3].iter()
            .map(|&m| (m, receiver, val(100))).collect();
        commit(&mut d, 9, &forwarded);
        if with_late_transfers {
            let late: Vec<_> = intermediaries[..3].iter()
                .map(|&m| (s, m, val(50))).collect();
            commit(&mut d, 10, &late);
        }
        d.block_caches.clear();
        d.overlay.clear();
        d
    }

    #[test]
    fn validator_specific_seeds_differ_and_are_reproducible() {
        let cfg = sampling(16);
        let seed = derive_sampling_seed(&cfg, &context(), SampledMotifKind::FanIn, 0);
        assert_eq!(seed, derive_sampling_seed(&cfg, &context(), SampledMotifKind::FanIn, 0));
        let mut other = cfg.clone();
        other.validator_id = hash(0xa2);
        assert_ne!(seed, derive_sampling_seed(&other, &context(), SampledMotifKind::FanIn, 0));
    }

    #[test]
    fn priority_sample_is_deterministic_and_budget_nested() {
        let mut candidates: Vec<Address> = (1..=60).map(addr).collect();
        let seed = hash(0x11);
        let mut small = BinaryHeap::new();
        let mut large = BinaryHeap::new();
        for &a in &candidates {
            keep_priority(&mut small, seed, a, 8);
            keep_priority(&mut large, seed, a, 25);
        }
        let small: Vec<_> = small.into_sorted_vec().into_iter().map(|x| x.1).collect();
        let large: Vec<_> = large.into_sorted_vec().into_iter().map(|x| x.1).collect();
        assert_eq!(&large[..8], &small);
        candidates.reverse();
        let mut reordered = BinaryHeap::new();
        for a in candidates { keep_priority(&mut reordered, seed, a, 8); }
        let reordered: Vec<_> = reordered.into_sorted_vec().into_iter()
            .map(|x| x.1).collect();
        assert_eq!(reordered, small);
        assert_eq!(small.iter().copied().collect::<HashSet<_>>().len(), 8);
    }

    #[test]
    fn sg_temporal_cutoff_excludes_only_late_edges() {
        let d = sg_fixture(true);
        let (sum, latest) = d.sampled_sg_pair_through(addr(0x50), addr(21), 11, 9);
        assert_eq!(sum, val(100));
        assert_eq!(latest, 8);
        // The full rolling window also contains block-10 X->M deposits.
        let (full, _) = d.sampled_sg_pair_through(addr(0x50), addr(21), 11, 11);
        assert_eq!(full, val(150));
    }

    #[test]
    fn sg_discovers_and_verifies_paper_aligned_late_edge_witness() {
        let mut d = sg_fixture(true);
        let source = addr(0x50);
        let target_from = addr(24);
        let receiver = addr(0x90);
        let result = d.sampled_check_tx_all_motifs(
            addr(0xf0), target_from, receiver, val(100), 11, &sampling(20), &context()
        );
        let witness = result.witnesses.iter().find_map(|w| match &w.witness {
            AMLWitness::ScatterGather(sg) => Some(sg), _ => None,
        }).expect("SG must be detected when all 4 intermediaries and pairs fit budget");
        assert_eq!(witness.source, source);
        assert_eq!(witness.branches.len(), 4);
        assert!(result.total_metrics.pair_sum_evaluations <= 20);
        let evidence = AMLWitness::ScatterGather(witness.clone());
        assert!(d.verify_aml_witness_for_tx(&evidence, &witness.target));

        let mut wrong_tx = witness.target.clone();
        wrong_tx.tx_index += 1;
        assert!(!d.verify_aml_witness_for_tx(&evidence, &wrong_tx));
        wrong_tx = witness.target.clone();
        wrong_tx.token = addr(0xee);
        assert!(!d.verify_aml_witness_for_tx(&evidence, &wrong_tx));
        wrong_tx = witness.target.clone();
        wrong_tx.block_hash = hash(0x99);
        assert!(!d.verify_aml_witness_for_tx(&evidence, &wrong_tx));

        let mut altered = witness.clone();
        altered.branches[0].source_to_intermediary.from = addr(0xee);
        assert!(!d.verify_aml_witness_for_tx(
            &AMLWitness::ScatterGather(altered), &witness.target
        ));

        // The reference exact detector must flag the same candidate.
        let mut exact = sg_fixture(true);
        let indices = exact.consensus_validate_block(
            &[(addr(0xf0), target_from, receiver, val(100))], 11, B256::ZERO
        );
        assert_eq!(indices, vec![0]);
    }

    #[test]
    fn full_budget_fan_in_fan_out_and_gs_witnesses_verify() {
        // Fan-In: fourth distinct sender triggers count/amount threshold.
        let mut cfg = config();
        cfg.fan_in_count_threshold = 3;
        cfg.fan_in_sum_threshold = val(350);
        let mut d = AMLMotifDetector::new(cfg);
        let r = addr(0x70);
        commit(&mut d, 9, &[
            (addr(1), r, val(100)), (addr(2), r, val(100)),
            (addr(3), r, val(100)),
        ]);
        let mut b = sampling(0);
        b.fan_in_budget = 4;
        let result = d.sampled_check_tx_all_motifs(
            addr(0xf0), addr(4), r, val(100), 11, &b, &context(),
        );
        let fan_in = result.witnesses.iter().find(|w|
            matches!(&w.witness, AMLWitness::FanIn(_))).expect("FI witness");
        let expected = match &fan_in.witness {
            AMLWitness::FanIn(w) => &w.target, _ => unreachable!(),
        };
        assert!(d.verify_aml_witness_for_tx(&fan_in.witness, expected));
        let mut tampered = fan_in.witness.clone();
        if let AMLWitness::FanIn(w) = &mut tampered { w.center = addr(0xff); }
        assert!(!d.verify_aml_witness_for_tx(&tampered, expected));

        // Fan-Out: fourth destination triggers count/amount threshold.
        let mut cfg = config();
        cfg.fan_out_count_threshold = 3;
        cfg.fan_out_sum_threshold = val(350);
        let mut d = AMLMotifDetector::new(cfg);
        let h = addr(0x71);
        commit(&mut d, 9, &[
            (h, addr(1), val(100)), (h, addr(2), val(100)),
            (h, addr(3), val(100)),
        ]);
        let mut b = sampling(0);
        b.fan_out_budget = 4;
        let result = d.sampled_check_tx_all_motifs(
            addr(0xf0), h, addr(4), val(100), 11, &b, &context(),
        );
        let fan_out = result.witnesses.iter().find(|w|
            matches!(&w.witness, AMLWitness::FanOut(_))).expect("FO witness");
        let expected = match &fan_out.witness {
            AMLWitness::FanOut(w) => &w.target, _ => unreachable!(),
        };
        assert!(d.verify_aml_witness_for_tx(&fan_out.witness, expected));

        // Gather-Scatter: four active source and destination relationships.
        let mut d = AMLMotifDetector::new(config());
        let hub = addr(0x72);
        let mut edges = Vec::new();
        for i in 1..=4 { edges.push((addr(i), hub, val(100))); }
        for i in 11..=13 { edges.push((hub, addr(i), val(100))); }
        commit(&mut d, 9, &edges);
        let mut b = sampling(0);
        b.fan_out_budget = 4;
        b.gather_scatter_budget = 4;
        let mut cfg = d.config.clone();
        cfg.gather_scatter_count_threshold = 3;
        cfg.gather_scatter_threshold = val(350);
        d.config = cfg;
        let result = d.sampled_check_tx_all_motifs(
            addr(0xf0), hub, addr(14), val(100), 11, &b, &context(),
        );
        let gs = result.witnesses.iter().find(|w|
            matches!(&w.witness, AMLWitness::GatherScatter(_))).expect("GS witness");
        let expected = match &gs.witness {
            AMLWitness::GatherScatter(w) => &w.target, _ => unreachable!(),
        };
        assert!(d.verify_aml_witness_for_tx(&gs.witness, expected));
    }

    #[test]
    fn zero_budgets_do_no_pair_evaluations() {
        let mut d = sg_fixture(false);
        let result = d.sampled_check_tx_all_motifs(
            addr(0xf0), addr(24), addr(0x90), val(100), 11,
            &sampling(0), &context(),
        );
        assert!(!result.found_any());
        assert_eq!(result.total_metrics.pair_sum_evaluations, 0);
    }

//     #[test]
//     #[ignore = "manual history-depth benchmark; writes CSV"]
//     fn sampling_history_depth_benchmark() {
//         use std::{
//             fs::{create_dir_all, File},
//             hint::black_box,
//             io::{BufWriter, Write},
//             path::PathBuf,
//             time::Instant,
//         };
//
//         const ITERATIONS: usize = 30;
//
//         let shapes = [
//             HistoryBenchShape::FanIn,
//             HistoryBenchShape::FanOut,
//             HistoryBenchShape::GatherScatter,
//             HistoryBenchShape::ScatterGather,
//         ];
//         let degrees = [128usize, 512];
//         let history_depths = [1usize, 4, 16, 64];
//         let budgets = [32usize, 64, 128];
//
//         let output_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
//             .join("src")
//             .join("aml_graph")
//             .join("test_results");
//         create_dir_all(&output_dir).expect("create test-results directory");
//
//         let output_path = output_dir.join("aml_sampling_history_depth.csv");
//         let mut writer = BufWriter::new(
//             File::create(&output_path).expect("create history-depth CSV"),
//         );
//
//         writeln!(
//             writer,
//             "shape,degree,history_edges_per_pair,budget,iterations,\
// exact_mean_ns,exact_p50_ns,exact_p95_ns,\
// sampled_mean_ns,sampled_p50_ns,sampled_p95_ns,\
// speedup_exact_over_sampled,\
// avg_candidate_count,avg_pair_sum_evaluations,avg_sg_branch_evaluations"
//         )
//             .unwrap();
//
//         for shape in shapes {
//             for degree in degrees {
//                 for history_depth in history_depths {
//                     let (
//                         mut detector,
//                         token,
//                         from,
//                         to,
//                         amount,
//                         block,
//                     ) = build_history_depth_fixture(
//                         shape,
//                         degree,
//                         history_depth,
//                     );
//
//                     for budget in budgets {
//                         let sampling = SamplingConfig {
//                             fan_in_budget: budget,
//                             fan_out_budget: budget,
//                             gather_scatter_budget: budget,
//                             scatter_gather_budget: budget,
//                             validator_id: B256::from([0x11; 32]),
//                             randomness: B256::from([0x22; 32]),
//                         };
//                         let context = SamplingContext {
//                             block_hash: B256::from([0x33; 32]),
//                             block_number: block,
//                             tx_index: 0,
//                         };
//
//                         let mut exact_times = Vec::with_capacity(ITERATIONS);
//                         let mut sampled_times = Vec::with_capacity(ITERATIONS);
//                         let mut candidate_total = 0u128;
//                         let mut pair_total = 0u128;
//                         let mut branch_total = 0u128;
//
//                         for iteration in 0..ITERATIONS {
//                             // Alternate order to reduce systematic first-run bias.
//                             let sampled_first = iteration % 2 == 0;
//
//                             if sampled_first {
//                                 detector.block_caches.clear();
//                                 detector.overlay.clear();
//                                 let start = Instant::now();
//                                 let sampled = detector.sampled_check_tx_all_motifs(
//                                     token,
//                                     from,
//                                     to,
//                                     amount,
//                                     block,
//                                     &sampling,
//                                     &context,
//                                 );
//                                 sampled_times.push(start.elapsed().as_nanos());
//                                 assert!(!sampled.found_any());
//                                 candidate_total +=
//                                     sampled.total_metrics.candidate_count as u128;
//                                 pair_total += sampled
//                                     .total_metrics
//                                     .pair_sum_evaluations as u128;
//                                 branch_total += sampled
//                                     .total_metrics
//                                     .sg_branch_evaluations as u128;
//                                 black_box(sampled);
//
//                                 detector.block_caches.clear();
//                                 detector.overlay.clear();
//                                 let start = Instant::now();
//                                 let exact = detector.would_be_suspicious(
//                                     token, from, to, amount, block,
//                                 );
//                                 exact_times.push(start.elapsed().as_nanos());
//                                 assert!(!exact.0.is_suspicious());
//                                 assert!(!exact.1.is_suspicious());
//                                 black_box(exact);
//                             } else {
//                                 detector.block_caches.clear();
//                                 detector.overlay.clear();
//                                 let start = Instant::now();
//                                 let exact = detector.would_be_suspicious(
//                                     token, from, to, amount, block,
//                                 );
//                                 exact_times.push(start.elapsed().as_nanos());
//                                 assert!(!exact.0.is_suspicious());
//                                 assert!(!exact.1.is_suspicious());
//                                 black_box(exact);
//
//                                 detector.block_caches.clear();
//                                 detector.overlay.clear();
//                                 let start = Instant::now();
//                                 let sampled = detector.sampled_check_tx_all_motifs(
//                                     token,
//                                     from,
//                                     to,
//                                     amount,
//                                     block,
//                                     &sampling,
//                                     &context,
//                                 );
//                                 sampled_times.push(start.elapsed().as_nanos());
//                                 assert!(!sampled.found_any());
//                                 candidate_total +=
//                                     sampled.total_metrics.candidate_count as u128;
//                                 pair_total += sampled
//                                     .total_metrics
//                                     .pair_sum_evaluations as u128;
//                                 branch_total += sampled
//                                     .total_metrics
//                                     .sg_branch_evaluations as u128;
//                                 black_box(sampled);
//                             }
//                         }
//
//                         let exact_mean =
//                             exact_times.iter().sum::<u128>() / ITERATIONS as u128;
//                         let sampled_mean =
//                             sampled_times.iter().sum::<u128>() / ITERATIONS as u128;
//                         let exact_p50 = hd_percentile(&mut exact_times, 0.50);
//                         let exact_p95 = hd_percentile(&mut exact_times, 0.95);
//                         let sampled_p50 = hd_percentile(&mut sampled_times, 0.50);
//                         let sampled_p95 = hd_percentile(&mut sampled_times, 0.95);
//
//                         writeln!(
//                             writer,
//                             "{:?},{},{},{},{},{},{},{},{},{},{},{:.6},{:.3},{:.3},{:.3}",
//                             shape,
//                             degree,
//                             history_depth,
//                             budget,
//                             ITERATIONS,
//                             exact_mean,
//                             exact_p50,
//                             exact_p95,
//                             sampled_mean,
//                             sampled_p50,
//                             sampled_p95,
//                             exact_mean as f64 / sampled_mean.max(1) as f64,
//                             candidate_total as f64 / ITERATIONS as f64,
//                             pair_total as f64 / ITERATIONS as f64,
//                             branch_total as f64 / ITERATIONS as f64,
//                         )
//                             .unwrap();
//                     }
//                 }
//             }
//         }
//
//         writer.flush().unwrap();
//         println!(
//             "history-depth results written to {}",
//             output_path.display()
//         );
//     }


    // Full-budget differential coverage. These tests intentionally isolate each
    // motif so an earlier check cannot mask the motif under test.
    #[derive(Clone, Copy, Debug)]
    enum DifferentialMotif {
        FanIn,
        FanOut,
        GatherScatter,
        ScatterGather,
    }

    fn differential_fixture(
        motif: DifferentialMotif,
        degree: u8,
        amount: u64,
        count_threshold: u64,
        sum_threshold: u64,
        late_sg_edges: bool,
    ) -> (AMLMotifDetector, Address, Address) {
        assert!(degree > 0 && degree < 20);
        let mut cfg = config();
        // Disable competing motifs for these small fixtures.
        cfg.fan_in_count_threshold = 100;
        cfg.fan_out_count_threshold = 100;
        cfg.gather_scatter_count_threshold = 100;
        cfg.scatter_gather_count_threshold = 100;
        cfg.fan_in_sum_threshold = val(100_000);
        cfg.fan_out_sum_threshold = val(100_000);
        cfg.gather_scatter_threshold = val(100_000);
        cfg.scatter_gather_threshold = val(100_000);
        match motif {
            DifferentialMotif::FanIn => {
                cfg.fan_in_count_threshold = count_threshold;
                cfg.fan_in_sum_threshold = val(sum_threshold);
            }
            DifferentialMotif::FanOut => {
                cfg.fan_out_count_threshold = count_threshold;
                cfg.fan_out_sum_threshold = val(sum_threshold);
            }
            DifferentialMotif::GatherScatter => {
                cfg.gather_scatter_count_threshold = count_threshold;
                cfg.gather_scatter_threshold = val(sum_threshold);
            }
            DifferentialMotif::ScatterGather => {
                cfg.scatter_gather_count_threshold = count_threshold;
                cfg.scatter_gather_threshold = val(sum_threshold);
            }
        }
        let mut d = AMLMotifDetector::new(cfg);
        let hub = addr(0x70);
        let source = addr(0x50);
        let receiver = addr(0x90);
        let candidate = match motif {
            DifferentialMotif::FanIn => {
                let edges: Vec<_> = (1..degree)
                    .map(|i| (addr(i), receiver, val(amount))).collect();
                commit(&mut d, 9, &edges);
                (addr(degree), receiver)
            }
            DifferentialMotif::FanOut => {
                let edges: Vec<_> = (1..degree)
                    .map(|i| (hub, addr(i), val(amount))).collect();
                commit(&mut d, 9, &edges);
                (hub, addr(degree))
            }
            DifferentialMotif::GatherScatter => {
                let incoming: Vec<_> = (1..=degree)
                    .map(|i| (addr(i), hub, val(amount))).collect();
                commit(&mut d, 8, &incoming);
                let outgoing: Vec<_> = (1..degree)
                    .map(|i| (hub, addr(30 + i), val(amount))).collect();
                commit(&mut d, 9, &outgoing);
                (hub, addr(30 + degree))
            }
            DifferentialMotif::ScatterGather => {
                let incoming: Vec<_> = (1..=degree)
                    .map(|i| (source, addr(i), val(amount))).collect();
                commit(&mut d, 8, &incoming);
                let outgoing: Vec<_> = (1..degree)
                    .map(|i| (addr(i), receiver, val(amount))).collect();
                commit(&mut d, 9, &outgoing);
                if late_sg_edges {
                    // These deposits must not inflate already-forwarded branches.
                    let late: Vec<_> = (1..degree)
                        .map(|i| (source, addr(i), val(50))).collect();
                    commit(&mut d, 10, &late);
                }
                (addr(degree), receiver)
            }
        };
        d.block_caches.clear();
        d.overlay.clear();
        (d, candidate.0, candidate.1)
    }

    fn assert_full_budget_differential(motif: DifferentialMotif) {
        // name, degree, amount per pair, count threshold, amount threshold,
        // late SG deposits. Fan motifs use OR; GS and SG use AND.
        let cases = [
            ("clean_below_thresholds", 3u8, 100u64, 3u64, 350u64, false),
            ("both_thresholds_exceeded", 4, 100, 3, 350, false),
            ("count_only_exceeded", 4, 87, 3, 350, false),
            ("amount_only_exceeded", 3, 120, 3, 350, false),
            ("both_thresholds_equal", 4, 100, 4, 400, false),
            ("amount_equal_count_exceeded", 4, 100, 3, 400, false),
            ("count_equal_amount_exceeded", 4, 100, 4, 350, false),
            ("zero_amount_pairs", 4, 0, 3, 350, false),
            ("late_sg_deposits", 4, 100, 3, 350, true),
        ];
        for (name, degree, amount, count_threshold, sum_threshold, late) in cases {
            let (mut exact, from, to) = differential_fixture(
                motif, degree, amount, count_threshold, sum_threshold, late,
            );
            let (mut sampled, sampled_from, sampled_to) = differential_fixture(
                motif, degree, amount, count_threshold, sum_threshold, late,
            );
            assert_eq!((from, to), (sampled_from, sampled_to));
            let token = addr(0xf0);
            let ctx = context();
            // Independently constructed from the candidate, never the witness.
            let expected_tx = TargetTxEvidence {
                tx_index: ctx.tx_index,
                token,
                block_hash: ctx.block_hash,
                from,
                to,
                amount: val(amount),
                block: ctx.block_number,
            };
            let exact_indices = exact.consensus_validate_block(
                &[(token, from, to, val(amount))],
                ctx.block_number,
                ctx.block_hash,
            );
            let count_exceeded = amount > 0 && u64::from(degree) > count_threshold;
            let sum_exceeded = u64::from(degree) * amount > sum_threshold;
            let expected_detection = match motif {
                DifferentialMotif::FanIn | DifferentialMotif::FanOut =>
                    count_exceeded || sum_exceeded,
                DifferentialMotif::GatherScatter | DifferentialMotif::ScatterGather =>
                    count_exceeded && sum_exceeded,
            };
            assert_eq!(
                exact_indices,
                if expected_detection { vec![0] } else { vec![] },
                "exact oracle disagrees with fixture: {:?}/{}", motif, name,
            );
            // Finite bound exceeds all neighbor populations and the combined
            // SG right + left evaluations in these fixtures. Avoid usize::MAX:
            // SG computes (budget + 1) / 2 when scheduling lanes.
            let budget = usize::from(degree) * 3 + 8;
            let budgets = SamplingConfig {
                fan_in_budget: budget,
                fan_out_budget: budget,
                gather_scatter_budget: budget,
                scatter_gather_budget: budget,
                validator_id: hash(0xa1),
                randomness: hash(0x42),
            };
            // Several deterministic orders must all agree at full budget.
            for seed_byte in [0x11u8, 0x42, 0x93, 0xfe] {
                sampled.block_caches.clear();
                sampled.overlay.clear();
                let mut sampling_cfg = budgets.clone();
                sampling_cfg.randomness = hash(seed_byte);
                let result = sampled.sampled_check_tx_all_motifs(
                    token, from, to, val(amount), ctx.block_number,
                    &sampling_cfg, &ctx,
                );
                assert_eq!(result.found_any(), expected_detection,
                           "sampled/exact mismatch: {:?}/{}/seed={}", motif, name, seed_byte);
                for discovered in &result.witnesses {
                    let right_kind = matches!(
                        (motif, &discovered.witness),
                        (DifferentialMotif::FanIn, AMLWitness::FanIn(_))
                        | (DifferentialMotif::FanOut, AMLWitness::FanOut(_))
                        | (DifferentialMotif::GatherScatter, AMLWitness::GatherScatter(_))
                        | (DifferentialMotif::ScatterGather, AMLWitness::ScatterGather(_))
                    );
                    assert!(right_kind, "competing motif masked {:?}/{}", motif, name);
                    assert!(sampled.verify_aml_witness_for_tx(
                        &discovered.witness, &expected_tx,
                    ), "invalid witness: {:?}/{}/seed={}", motif, name, seed_byte);
                }
            }
        }
    }

    #[test]
    fn full_budget_differential_fan_in() {
        assert_full_budget_differential(DifferentialMotif::FanIn);
    }

    #[test]
    fn full_budget_differential_fan_out() {
        assert_full_budget_differential(DifferentialMotif::FanOut);
    }

    #[test]
    fn full_budget_differential_gather_scatter() {
        assert_full_budget_differential(DifferentialMotif::GatherScatter);
    }

    #[test]
    fn full_budget_differential_scatter_gather() {
        assert_full_budget_differential(DifferentialMotif::ScatterGather);
    }

    mod sampling_cost_diagnostic {
        use super::*;
        use std::hint::black_box;
        use std::time::Instant;

        const REPEATS: usize = 11;
        const SG_SOURCES: usize = 16;

        #[derive(Clone, Copy, Debug)]
        enum Shape {
            FanOut,
            FanIn,
            GatherScatter,
            ScatterGather,
        }

        struct Fixture {
            detector: AMLMotifDetector,
            from: Address,
            to: Address,
            block: u64,

            // Top-level neighborhoods used by this fixture.
            neighborhoods: Vec<(Address, petgraph::Direction)>,

            // One intermediary for the separate SG helper comparison.
            sg_intermediary: Option<Address>,
        }

        fn address(n: u64) -> Address {
            let mut bytes = [0u8; 20];
            bytes[12..].copy_from_slice(&n.to_be_bytes());
            Address::from(bytes)
        }

        fn build_fixture(
            shape: Shape,
            degree: usize,
            history_depth: u64,
            overlay_rounds: usize,
        ) -> Fixture {
            let cfg = Config {
                window_blocks: history_depth + 10,
                fan_in_count_threshold: u64::MAX,
                fan_in_sum_threshold: U256::MAX,
                fan_out_count_threshold: u64::MAX,
                fan_out_sum_threshold: U256::MAX,
                gather_scatter_count_threshold: u64::MAX,
                gather_scatter_threshold: U256::MAX,
                scatter_gather_count_threshold: u64::MAX,
                scatter_gather_threshold: U256::MAX,
            };

            let mut detector = AMLMotifDetector::new(cfg);
            let hub = address(1);
            let receiver = address(2);
            let token = address(3);
            let amount = U256::from(1u64);
            let mut pairs = Vec::new();

            let (from, to, neighborhoods, sg_intermediary) = match shape {
                Shape::FanOut => {
                    for i in 0..degree {
                        pairs.push((hub, address(1_000 + i as u64)));
                    }
                    (
                        hub,
                        address(1_000),
                        vec![(hub, Outgoing)],
                        None,
                    )
                }

                Shape::FanIn => {
                    for i in 0..degree {
                        pairs.push((address(1_000 + i as u64), receiver));
                    }
                    (
                        address(1_000),
                        receiver,
                        vec![(receiver, Incoming)],
                        None,
                    )
                }

                Shape::GatherScatter => {
                    for i in 0..degree {
                        pairs.push((address(1_000 + i as u64), hub));
                        pairs.push((hub, address(10_000 + i as u64)));
                    }
                    (
                        hub,
                        address(10_000),
                        vec![(hub, Outgoing), (hub, Incoming)],
                        None,
                    )
                }

                Shape::ScatterGather => {
                    for i in 0..degree {
                        let intermediary = address(1_000 + i as u64);
                        pairs.push((intermediary, receiver));

                        for j in 0..SG_SOURCES {
                            let source = address(100_000 + j as u64);
                            pairs.push((source, intermediary));
                        }
                    }
                    (
                        address(1_000),
                        receiver,
                        vec![(receiver, Incoming)],
                        Some(address(1_000)),
                    )
                }
            };

            // Construction is outside all timed regions.
            let txs: Vec<_> = pairs
                .iter()
                .map(|&(a, b)| (token, a, b, amount))
                .collect();

            for h in 1..=history_depth {
                detector.block_commit(h, B256::ZERO, &txs);
            }

            let block = history_depth + 2;

            // Populate an accepted-prefix overlay without running AML checks.
            // Leave neighbor caches empty so their first build sees all state.
            for _ in 0..overlay_rounds {
                for &(a, b) in &pairs {
                    detector.overlay.append(
                        a,
                        b,
                        TransferEdge { amount, block },
                    );
                }
            }

            detector.block_caches.clear();

            Fixture {
                detector,
                from,
                to,
                block,
                neighborhoods,
                sg_intermediary,
            }
        }

        // Median duration of a whole operation, in microseconds.
        // Preparation and result destruction are outside the timed region.
        fn median_us<P, F, R>(
            detector: &mut AMLMotifDetector,
            mut prepare: P,
            mut operation: F,
        ) -> f64
        where
            P: FnMut(&mut AMLMotifDetector),
            F: FnMut(&mut AMLMotifDetector) -> R,
        {
            let mut times = Vec::with_capacity(REPEATS);

            // Untimed warm-up of code paths and allocator.
            prepare(detector);
            black_box(operation(detector));

            for _ in 0..REPEATS {
                prepare(detector);

                let start = Instant::now();
                let result = black_box(operation(detector));
                let elapsed = start.elapsed();

                times.push(elapsed.as_nanos());
                drop(result);
            }

            times.sort_unstable();
            times[times.len() / 2] as f64 / 1_000.0
        }

        fn ensure_top_neighbors(
            detector: &mut AMLMotifDetector,
            neighborhoods: &[(Address, petgraph::Direction)],
        ) {
            for &(a, direction) in neighborhoods {
                detector.ensure_neighbors_cached(a, direction);
            }
        }

        fn select_top_pairs(
            detector: &mut AMLMotifDetector,
            neighborhoods: &[(Address, petgraph::Direction)],
            allowance: usize,
            seed: B256,
        ) -> Vec<(Address, Address)> {
            let mut pairs = Vec::new();

            for &(center, direction) in neighborhoods {
                let (neighbors, _) = detector.sampled_neighbors(
                    center,
                    direction,
                    None,
                    allowance,
                    seed,
                );

                for neighbor in neighbors {
                    let pair = match direction {
                        Incoming => (neighbor, center),
                        Outgoing => (center, neighbor),
                    };
                    pairs.push(pair);
                }
            }

            pairs
        }

        fn evaluate_pairs(
            detector: &mut AMLMotifDetector,
            pairs: &[(Address, Address)],
            block: u64,
        ) -> U256 {
            let mut sum = U256::ZERO;
            for &(a, b) in pairs {
                sum += detector.window_sum_full(a, b, block, None).0;
            }
            sum
        }

        fn exact_probe(
            detector: &mut AMLMotifDetector,
            from: Address,
            to: Address,
            block: u64,
        ) -> bool {
            let (sender, receiver) = detector.would_be_suspicious(
                address(3),
                from,
                to,
                U256::from(1u64),
                block,
            );
            sender.is_suspicious() || receiver.is_suspicious()
        }

        fn sampled_probe(
            detector: &mut AMLMotifDetector,
            from: Address,
            to: Address,
            block: u64,
            cfg: &SamplingConfig,
            ctx: &SamplingContext,
        ) -> SampledCheckResult {
            detector.sampled_check_tx_all_motifs(
                address(3),
                from,
                to,
                U256::from(1u64),
                block,
                cfg,
                ctx,
            )
        }

        #[test]
        #[ignore = "manual performance diagnostic; run in release mode"]
        fn sampling_cost_breakdown() {
            println!("\nAll durations are median microseconds.");
            println!("Synthetic fixtures; thresholds disabled; no early exits.");
            println!("Cold/warm refer to application caches, not CPU caches.");
            println!("Component timings are isolated probes, NOT additive totals.");

            for shape in [
                Shape::FanOut,
                Shape::FanIn,
                Shape::GatherScatter,
                Shape::ScatterGather,
            ] {
                for degree in [128usize, 512] {
                    for history_depth in [1u64, 16] {
                        for overlay_rounds in [0usize, 4] {
                            let Fixture {
                                mut detector,
                                from,
                                to,
                                block,
                                neighborhoods,
                                sg_intermediary,
                            } = build_fixture(
                                shape,
                                degree,
                                history_depth,
                                overlay_rounds,
                            );

                            let ctx = SamplingContext {
                                block_hash: B256::from([0x88; 32]),
                                block_number: block,
                                tx_index: 0,
                            };

                            println!(
                                "\n{:?}: degree={}, history={}, overlay_rounds={}",
                                shape, degree, history_depth, overlay_rounds,
                            );

                            // 1. Initial construction of top-level neighbor caches.
                            let cache_build = median_us(
                                &mut detector,
                                |d| d.block_caches.clear(),
                                |d| {
                                    ensure_top_neighbors(d, &neighborhoods);
                                    black_box(&d.block_caches);
                                },
                            );

                            println!(
                                "  top-level neighbor-cache build: {:.3} us",
                                cache_build,
                            );

                            for allowance in [8usize, 32] {
                                let cfg = SamplingConfig {
                                    fan_in_budget: allowance,
                                    fan_out_budget: allowance,
                                    gather_scatter_budget: allowance,
                                    scatter_gather_budget: allowance,
                                    validator_id: B256::from([0xa1; 32]),
                                    randomness: B256::from([0x42; 32]),
                                };

                                let seed = derive_sampling_seed(
                                    &cfg,
                                    &ctx,
                                    SampledMotifKind::FanOut,
                                    0,
                                );

                                // 2. Selection with neighborhood construction excluded.
                                let selection = median_us(
                                    &mut detector,
                                    |d| {
                                        ensure_top_neighbors(d, &neighborhoods);
                                    },
                                    |d| {
                                        select_top_pairs(
                                            d, &neighborhoods, allowance, seed,
                                        )
                                    },
                                );

                                let selected = select_top_pairs(
                                    &mut detector,
                                    &neighborhoods,
                                    allowance,
                                    seed,
                                );

                                assert_eq!(
                                selected.len(),
                                neighborhoods.len() * allowance.min(degree),
                            );

                                // 3. Same selected pairs: cold historical pair cache.
                                let pairs_cold = median_us(
                                    &mut detector,
                                    |d| d.block_caches.base_pair_sum.clear(),
                                    |d| evaluate_pairs(d, &selected, block),
                                );

                                // 4. Same selected pairs: historical sums already cached.
                                let pairs_warm = median_us(
                                    &mut detector,
                                    |d| {
                                        black_box(evaluate_pairs(d, &selected, block));
                                    },
                                    |d| evaluate_pairs(d, &selected, block),
                                );

                                println!(
                                    "  allowance={}: top_select={:.3}, \
                                 selected_pairs={}, pairs_cold={:.3}, \
                                 pairs_warm={:.3} us",
                                    allowance,
                                    selection,
                                    selected.len(),
                                    pairs_cold,
                                    pairs_warm,
                                );

                                // 5. Actual complete entry points.
                                // Each path receives independently prepared caches.
                                for mode in 0..3 {
                                    let mode_name = match mode {
                                        0 => "first_access",
                                        1 => "neighbors_warm_pairs_cold",
                                        _ => "repeated_access",
                                    };

                                    let measure_exact = |d: &mut AMLMotifDetector| {
                                        median_us(
                                            d,
                                            |d| {
                                                d.block_caches.clear();

                                                if mode != 0 {
                                                    black_box(exact_probe(
                                                        d, from, to, block,
                                                    ));
                                                    if mode == 1 {
                                                        d.block_caches
                                                            .base_pair_sum.clear();
                                                    }
                                                }
                                            },
                                            |d| exact_probe(d, from, to, block),
                                        )
                                    };

                                    let measure_sampled = |d: &mut AMLMotifDetector| {
                                        median_us(
                                            d,
                                            |d| {
                                                d.block_caches.clear();

                                                if mode != 0 {
                                                    black_box(sampled_probe(
                                                        d, from, to, block,
                                                        &cfg, &ctx,
                                                    ));
                                                    if mode == 1 {
                                                        d.block_caches
                                                            .base_pair_sum.clear();
                                                    }
                                                }
                                            },
                                            |d| sampled_probe(
                                                d, from, to, block, &cfg, &ctx,
                                            ),
                                        )
                                    };

                                    // Alternate ordering across configurations.
                                    let (exact_us, sampled_us) =
                                        if (degree + allowance
                                            + history_depth as usize
                                            + overlay_rounds + mode) % 2 == 0
                                        {
                                            let e = measure_exact(&mut detector);
                                            let s = measure_sampled(&mut detector);
                                            (e, s)
                                        } else {
                                            let s = measure_sampled(&mut detector);
                                            let e = measure_exact(&mut detector);
                                            (e, s)
                                        };

                                    // Sanity checks outside timed regions.
                                    detector.block_caches.clear();
                                    assert!(!exact_probe(
                                        &mut detector, from, to, block,
                                    ));

                                    detector.block_caches.clear();
                                    let result = sampled_probe(
                                        &mut detector,
                                        from,
                                        to,
                                        block,
                                        &cfg,
                                        &ctx,
                                    );
                                    assert!(!result.found_any());

                                    println!(
                                        "    {}: exact={:.3}, sampled={:.3} us, \
                                     speedup={:.3}x, candidates={}, \
                                     pair_evals={}, sg_branches={}",
                                        mode_name,
                                        exact_us,
                                        sampled_us,
                                        exact_us / sampled_us.max(0.001),
                                        result.total_metrics.candidate_count,
                                        result.total_metrics.pair_sum_evaluations,
                                        result.total_metrics.sg_branch_evaluations,
                                    );
                                }
                            }

                            // 6. SG-specific comparison for ONE intermediary.
                            // Compare selected-source pair scans against exact
                            // aggregation of ALL sources in a single pass.
                            if let Some(intermediary) = sg_intermediary {
                                let cutoff = if overlay_rounds > 0 {
                                    block
                                } else {
                                    history_depth
                                };

                                detector.ensure_neighbors_cached(
                                    intermediary, Incoming,
                                );

                                let (sources, population) =
                                    detector.sampled_neighbors(
                                        intermediary,
                                        Incoming,
                                        None,
                                        8,
                                        B256::from([0x55; 32]),
                                    );

                                assert_eq!(population, SG_SOURCES);

                                let sampled_left = median_us(
                                    &mut detector,
                                    |_| {},
                                    |d| {
                                        let mut total = U256::ZERO;
                                        for &source in &sources {
                                            total += d.sampled_sg_pair_through(
                                                source,
                                                intermediary,
                                                block,
                                                cutoff,
                                            ).0;
                                        }
                                        total
                                    },
                                );

                                let mut all_sources = FxHashMap::default();
                                let exact_left = median_us(
                                    &mut detector,
                                    |_| {},
                                    |d| {
                                        d.sg_left_by_source(
                                            intermediary,
                                            block,
                                            cutoff,
                                            &mut all_sources,
                                        );
                                        black_box(&all_sources);
                                    },
                                );

                                // Verify helper agreement for every sampled source.
                                detector.sg_left_by_source(
                                    intermediary,
                                    block,
                                    cutoff,
                                    &mut all_sources,
                                );

                                for &source in &sources {
                                    let actual = detector.sampled_sg_pair_through(
                                        source,
                                        intermediary,
                                        block,
                                        cutoff,
                                    ).0;

                                    assert_eq!(
                                    actual,
                                    *all_sources.get(&source).unwrap(),
                                );
                                }

                                println!(
                                    "  SG one-intermediary helper: \
                                 sampled_{}_sources={:.3} us, \
                                 exact_all_{}_sources={:.3} us",
                                    sources.len(),
                                    sampled_left,
                                    SG_SOURCES,
                                    exact_left,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

}
