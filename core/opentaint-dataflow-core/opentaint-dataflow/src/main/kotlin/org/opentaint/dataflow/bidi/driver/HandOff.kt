package org.opentaint.dataflow.bidi.driver

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.RunConfig
import org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer
import org.opentaint.dataflow.bidi.engine.RunResult
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.engine.SharedObjects
import org.opentaint.dataflow.bidi.interp.SinkRule
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.FrozenStaticCompletion
import org.opentaint.dataflow.bidi.store.guidancePattern
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.Collections
import mu.KotlinLogging
import kotlin.time.TimeSource

/** Immutable outgoing demand, seeds and accepted explicit-pattern counts.
 * [of] counts only successful normalized builder insertions. Its method-key support is
 * empty exactly when the built explicit snapshot is empty; virtual static families are separate.
 * Manually constructed test values need not have that binding.
 */
class HandOff(val demand: DemandStore, val seeds: SeedIndex, demandEdges: Map<MethodKey, Int>) {
    val demandEdges: Map<MethodKey, Int> = Collections.unmodifiableMap(LinkedHashMap(demandEdges))

    companion object {
        private val logger = KotlinLogging.logger {}
        fun of(config: RunConfig, result: RunResult<RunMethodAnalyzer>, report: ReportBuilder,
               shared: SharedObjects): HandOff {
            check(result.status == RunStatus.COMPLETE) { "A hand-off needs a complete run" }
            shared.cancellation.checkpoint()
            val counts = LinkedHashMap<MethodKey, Int>()
            val (demand, seeds) = if (config.direction == Direction.FORWARD)
                toBackward(result, report, shared, counts, config.run1) else toForward(result, shared, counts)
            return HandOff(demand, seeds, counts)
        }

        private inline fun forEachDemandPiece(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                                             body: (MethodKey, PremiseKey, Pattern) -> Unit) {
            for (actor in result.analyzers) {
                shared.cancellation.checkpoint()
                for ((premise, facts) in actor.summaries.demandEdges()) {
                    shared.cancellation.checkpoint()
                    if (!actor.mode.run1 && facts is FlowTree && facts.layer == Layer.DEMAND)
                        check(facts.tail == Tail.ANY && facts.exclusion == ExclusionSet.Empty) {
                            "A restricted FLOW demand result must be ANY with empty field exclusions"
                        }
                    for (leaf in shared.ops.leaves(facts)) {
                        shared.cancellation.checkpoint()
                        body(actor.key, premise, leaf)
                    }
                }
            }
        }

        private fun toBackward(result: RunResult<RunMethodAnalyzer>, report: ReportBuilder, shared: SharedObjects,
                               counts: MutableMap<MethodKey, Int>, run1: Boolean): Pair<DemandStore, SeedIndex> {
            val demand = DemandStore.Builder(shared.ap)
            val completionStart = TimeSource.Monotonic.markNow()
            val joinedCompletion = if (run1) result.staticCompletion else null
            val completion = if (run1 && joinedCompletion == null)
                FrozenStaticCompletion.Builder(shared.ap, shared.staticCallGraph) else null
            if (run1) demand.withSharedStaticCarry()
            if (joinedCompletion != null) {
                demand.withCompletion(joinedCompletion)
                logger.info { "BIDI_STATIC_CLOSURE_HANDOFF run=1 source=JOINED ${joinedCompletion.statistics()}" }
            }
            // Synthetic frozen RunResults in small tests have no runner-owned
            // pre-release phase. Their fallback uses local seeds only; real
            // RunManager results supply the joined completion above.
            if (completion != null) {
                for (actor in result.analyzers) {
                    for (edge in actor.staticGuidanceSeeds.frozenRows()) {
                        shared.cancellation.checkpoint()
                        completion.addSeed(actor.key, edge)
                    }
                    for (key in actor.freezeStaticWriteCandidates().lostRows()) {
                        shared.cancellation.checkpoint()
                        completion.addSeed(actor.key, key.original.toPattern(), key.result)
                    }
                }
            }
            val seedCaptureTime = completionStart.elapsedNow()
            val projectionStart = TimeSource.Monotonic.markNow()
            forEachDemandPiece(result, shared) { method, premise, piece ->
                val entry = guidancePattern(piece)
                premise.forEachMember { member ->
                    shared.cancellation.checkpoint()
                    val from = guidancePattern(member.toPattern())
                    completion?.addBoundary(method, from, entry)
                    val pattern = DemandPattern(entry, from)
                    if (demand.add(method, pattern)) counts.merge(method, 1, Int::plus)
                }
            }
            if (completion != null) {
                val projectionTime = projectionStart.elapsedNow()
                val indexStart = TimeSource.Monotonic.markNow()
                val frozen = completion.build()
                demand.withCompletion(frozen)
                logger.info { "BIDI_STATIC_CLOSURE_FREEZE run=1 source=LOCAL_FROZEN_INPUT freezeTime=${completionStart.elapsedNow()} seedTime=$seedCaptureTime projectionTime=$projectionTime indexTime=${indexStart.elapsedNow()} ${frozen.statistics()}" }
            }
            val seeds = LinkedHashSet<Seed>()
            for (entry in report.demandEntries()) {
                shared.cancellation.checkpoint()
                val methods = LinkedHashSet<MethodKey>()
                for (witness in entry.witnesses) {
                    shared.cancellation.checkpoint()
                    methods += witness.methodKey
                }
                for (method in methods) {
                    shared.cancellation.checkpoint()
                    withSinksAt(shared, method, entry.key.statement) { sinks ->
                        for (sink in sinks) {
                            shared.cancellation.checkpoint()
                            if (sink.rule != entry.key.rule) continue
                            if (sink.predicate != null) {
                                if (!sink.unconditional)
                                    seeds += Seed.PredicateSink(checkNotNull(sink.occurrenceId), method, entry.key.statement)
                                continue
                            }
                            for (literal in sink.seedPatterns()) {
                                shared.cancellation.checkpoint()
                                seeds += Seed.Sink(entry.key.rule, method, entry.key.statement, literal)
                            }
                        }
                    }
                }
            }
            return demand.build() to SeedIndex.of(seeds.toList())
        }

        private fun withSinksAt(shared: SharedObjects, key: MethodKey, statement: CommonInst,
                                use: (List<SinkRule>) -> Unit) {
            val forms = shared.contexts.forms(key)
            val call = shared.language.getCallExpr(statement)
            if (call != null) {
                forms.withCall(Direction.FORWARD, statement, call) { use(it.sinks) }
            } else if (shared.interpreter.exitNodes(key).any { shared.cancellation.checkpoint(); it.node == statement }) {
                forms.withExitRules(Direction.FORWARD, statement) { use(it.rules.sinks) }
            }
        }

        private fun toForward(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                              counts: MutableMap<MethodKey, Int>): Pair<DemandStore, SeedIndex> {
            val demand = DemandStore.Builder(shared.ap)
            forEachDemandPiece(result, shared) { method, premise, piece ->
                val pattern = when (premise) {
                    is InitialAp -> DemandPattern(guidancePattern(piece),
                        if (premise.isZero) null else guidancePattern(premise.toPattern()))
                    is PremiseSet -> error("The backward run has no multi-premise summary (ap.md §9.2)")
                }
                if (demand.add(method, pattern)) counts.merge(method, 1, Int::plus)
            }
            val seeds = ArrayList<Seed>()
            for (actor in result.analyzers) {
                shared.cancellation.checkpoint()
                for ((method, statement, edge, action) in checkNotNull(actor.sourceHits).occurrences()) {
                    shared.cancellation.checkpoint()
                    seeds += Seed.Source(method, statement, edge, action)
                }
            }
            return demand.build() to SeedIndex.of(seeds)
        }
    }
}
