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
import org.opentaint.dataflow.bidi.store.DemandEntry
import org.opentaint.dataflow.bidi.store.DemandExit
import org.opentaint.dataflow.bidi.store.PairedDemand
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
        fun of(config: RunConfig, result: RunResult<RunMethodAnalyzer>, shared: SharedObjects): HandOff {
            check(result.status == RunStatus.COMPLETE) { "A hand-off needs a complete run" }
            shared.cancellation.checkpoint()
            val counts = LinkedHashMap<MethodKey, Int>()
            val (demand, seeds) = if (config.direction == Direction.FORWARD)
                toBackward(result, shared, counts, config.run1) else toForward(result, shared, counts)
            return HandOff(demand, seeds, counts)
        }

        private inline fun forEachDemandPiece(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                                             direction: Direction,
                                             body: (MethodKey, PremiseKey, Pattern) -> Unit) {
            for (actor in result.analyzers) {
                shared.cancellation.checkpoint()
                for ((premise, facts) in actor.summaries.demandEdges(direction)) {
                    shared.cancellation.checkpoint()
                    // Keep C5's STAR correlation. Projection uses the existing
                    // guidance normalization for selector E/mx and MUST.
                    for (leaf in shared.ops.leaves(facts)) {
                        shared.cancellation.checkpoint()
                        body(actor.key, premise, leaf)
                    }
                }
            }
        }

        private fun toBackward(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                               counts: MutableMap<MethodKey, Int>, run1: Boolean): Pair<DemandStore, SeedIndex> {
            val demand = DemandStore.Builder(shared.ap)
            val completionStart = TimeSource.Monotonic.markNow()
            val joinedCompletion = if (run1) result.staticCompletion else null
            val completion = if (run1 && joinedCompletion == null)
                FrozenStaticCompletion.Builder(shared.ap, shared.staticCallGraph) else null
            if (run1) demand.withSharedStaticCarry()
            if (joinedCompletion != null) {
                demand.withCompletion(joinedCompletion)
                for ((owner, view) in joinedCompletion.scopedViews())
                    demand.withCompletion(owner.method, owner.local, view)
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
                    for (terminal in actor.outgoingTargets) {
                        shared.cancellation.checkpoint()
                        check(terminal.target == org.opentaint.dataflow.bidi.engine.Target.DemandTarget)
                        val original = checkNotNull(terminal.premise as? InitialAp) { "Run-1 cannot retain an ND original" }
                        completion.addTarget(actor.key, original.toPattern())
                    }
                }
            }
            val seedCaptureTime = completionStart.elapsedNow()
            val projectionStart = TimeSource.Monotonic.markNow()
            forEachDemandPiece(result, shared, Direction.FORWARD) { method, premise, piece ->
                val entry = guidancePattern(piece)
                premise.forEachMember { member ->
                    shared.cancellation.checkpoint()
                    val from = guidancePattern(member.toPattern())
                    completion?.addBoundary(method, from, entry)
                    val pattern = DemandPattern(entry, from)
                    if (demand.add(method, pattern)) counts.merge(method, 1, Int::plus)
                }
            }
            projectTargets(result, shared, demand, counts)
            projectBlocks(result, shared, Direction.FORWARD, run1, demand, counts, completion)
            if (completion != null) {
                val projectionTime = projectionStart.elapsedNow()
                val indexStart = TimeSource.Monotonic.markNow()
                val frozen = completion.build()
                demand.withCompletion(frozen)
                for ((owner, view) in frozen.scopedViews()) demand.withCompletion(owner.method, owner.local, view)
                logger.info { "BIDI_STATIC_CLOSURE_FREEZE run=1 source=LOCAL_FROZEN_INPUT freezeTime=${completionStart.elapsedNow()} seedTime=$seedCaptureTime projectionTime=$projectionTime indexTime=${indexStart.elapsedNow()} ${frozen.statistics()}" }
            }
            val seeds = result.analyzers.flatMap { it.sinkSeeds }
            return demand.build() to SeedIndex.of(seeds)
        }

        private fun projectTargets(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                                   demand: DemandStore.Builder, counts: MutableMap<MethodKey, Int>) {
            for (actor in result.analyzers) for (row in actor.outgoingTargets) {
                shared.cancellation.checkpoint()
                for (member in row.premise.members) {
                    val exit = if (member.isZero) DemandExit.Zero
                        else DemandExit.Data(guidancePattern(member.toPattern()))
                    if (demand.add(actor.key, PairedDemand(DemandEntry.Target, exit)))
                        counts.merge(actor.key, 1, Int::plus)
                }
            }
        }

        private fun projectBlocks(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                                  direction: Direction, run1: Boolean,
                                  demand: DemandStore.Builder, counts: MutableMap<MethodKey, Int>,
                                  completion: FrozenStaticCompletion.Builder? = null) {
            projectBlockHandOff(shared.ap, direction, run1,
                result.analyzers.asSequence().flatMap { it.blockSummaries() },
                result.analyzers.asSequence().flatMap { it.blockOutgoingTargets() }, demand, counts,
                onBoundary = { key, from, to -> completion?.addScopedSeed(key, from, to) })
            if (run1 && completion != null) for (actor in result.analyzers)
                for (terminal in actor.blockOutgoingTargets()) for (row in terminal.rows) {
                    val original = checkNotNull(row.premise as? InitialAp) { "Run-1 cannot retain an ND original" }
                    completion.addScopedTarget(org.opentaint.dataflow.bidi.store.ScopedSummaryKey(
                        terminal.method, terminal.scope, terminal.exit), original.toPattern())
                }
        }

        private fun toForward(result: RunResult<RunMethodAnalyzer>, shared: SharedObjects,
                              counts: MutableMap<MethodKey, Int>): Pair<DemandStore, SeedIndex> {
            val demand = DemandStore.Builder(shared.ap)
            forEachDemandPiece(result, shared, Direction.BACKWARD) { method, premise, piece ->
                val pattern = when (premise) {
                    is InitialAp -> DemandPattern(guidancePattern(piece),
                        guidancePattern(premise.toPattern()))
                    is PremiseSet -> error("The backward run has no multi-premise summary (ap.md §9.2)")
                }
                if (demand.add(method, pattern)) counts.merge(method, 1, Int::plus)
            }
            projectTargets(result, shared, demand, counts)
            projectBlocks(result, shared, Direction.BACKWARD, false, demand, counts)
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

/** Use the same predicate handle and literal seeds as the previous handoff. */
internal fun sinkSeedsFor(sink: SinkRule, method: MethodKey, at: CommonInst): List<Seed> = when {
    sink.predicate != null && !sink.unconditional ->
        listOf(Seed.PredicateSink(checkNotNull(sink.occurrenceId), method, at))
    sink.predicate != null -> emptyList()
    else -> sink.seedPatterns().map { Seed.Sink(sink.rule, method, at, it) }
}

/** GROUP evaluation must retain the original FULL seed patterns, as before.
 * Read the existing full form; do not keep a second seed or rule cache. */
internal fun fullSinkSeedsFor(shared: SharedObjects, sink: SinkRule,
                              method: MethodKey, at: CommonInst): List<Seed> {
    val seeds = LinkedHashSet<Seed>()
    withSinksAt(shared, method, at) { sinks ->
        for (full in sinks) {
            shared.cancellation.checkpoint()
            if (full.rule == sink.rule) seeds += sinkSeedsFor(full, method, at)
        }
    }
    return seeds.toList()
}

/** Existing full-form lookup used by sink handoff before terminal reporting. */
private fun withSinksAt(shared: SharedObjects, key: MethodKey, statement: CommonInst,
                       use: (List<SinkRule>) -> Unit) {
    val forms = shared.contexts.forms(key)
    val call = shared.language.getCallExpr(statement)
    if (call != null) forms.withCall(Direction.FORWARD, statement, call) { use(it.sinks) }
    else if (shared.interpreter.exitNodes(key).any {
        shared.cancellation.checkpoint(); it.node == statement
    }) forms.withExitRules(Direction.FORWARD, statement) { use(it.rules.sinks) }
}
