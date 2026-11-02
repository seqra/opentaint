package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.FrozenCompletion
import org.opentaint.dataflow.bidi.store.FrozenStaticCompletion
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.OwnedScope
import org.opentaint.dataflow.bidi.store.ScopedSummaryKey
import org.opentaint.dataflow.graph.PortId
import kotlin.time.Duration
import kotlin.time.TimeSource

internal data class JoinedStaticGuidance(
    val completion: FrozenCompletion,
    val binding: JoinedStaticWriterBinding.Statistics,
    val observedCandidates: Long,
    val lostCandidates: Long,
    val peakCandidates: Long,
    val pruneTime: Duration,
    val writerTime: Duration,
    val closureFreezeTime: Duration,
)

/** Runs after successful runner join and before actor/subscription release.
 * Its only exports are immutable guidance and aggregate counters. */
internal fun completeJoinedStaticGuidance(
    config: RunConfig,
    shared: SharedObjects,
    actors: List<RunMethodAnalyzer>,
    storage: (MethodKey) -> SummaryStorage?,
    checkpoint: () -> Unit,
): JoinedStaticGuidance {
    check(config.run1)
    val builder = FrozenStaticCompletion.Builder(shared.ap, shared.staticCallGraph)
    val keys = shared.staticWriteKeyInterner
    val byMethod = actors.associateBy { it.key }
    fun seed(owner: OwnedScope, original: Pattern, output: Pattern, exit: PortId = PortId.STATIC_SHORTCUT) {
        if (owner.local == BlockScope.ROOT) builder.addSeed(owner.method, original, output)
        else builder.addScopedSeed(ScopedSummaryKey(owner.method, owner.local, exit), original, output)
    }
    val binding = OwnedJoinedStaticWriterBinding(shared.ops, config.mode, keys,
        borrow = { owner, writer, visit ->
            if (owner.local == BlockScope.ROOT) {
                storage(owner.method)?.visitJoinedInputs(writer, config.mode) { input ->
                    check(input.callee == owner.method) { "A writer can bind only its complete callee key" }
                    visit(OwnedWriterInput.call(input))
                }
            } else byMethod[owner.method]?.forEachJoinedLocalInput(owner.local) { link, actual ->
                checkpoint()
                check(link.child == owner.local) { "A joined local writer keeps its entry scope" }
                visit(OwnedWriterInput.local(owner.method, link, actual))
            }
        },
        onBound = { owner, original, output -> seed(owner, original.toPattern(), output) },
        checkpoint = checkpoint)
    var observed = 0L
    var lost = 0L
    var peak = 0L
    var pruneTime = Duration.ZERO
    for (actor in actors) for ((scope, state) in actor.joinedBlockStates()) {
        checkpoint()
        val owner = OwnedScope(actor.key, scope)
        val shortcut = ScopedSummaryKey(actor.key, scope, PortId.STATIC_SHORTCUT)
        if (scope != BlockScope.ROOT) builder.addScopedBoundary(shortcut)
        val pruneStarted = TimeSource.Monotonic.markNow()
        val writes = state.freezeStaticWriteCandidates()
        pruneTime += pruneStarted.elapsedNow()
        observed += writes.observedCount
        lost += writes.lostCount
        peak += writes.peakCount
        writes.forEachLostId { id ->
            checkpoint()
            val row = keys.row(id)
            seed(owner, row.original.toPattern(), row.result)
        }
        // Primitive writers bind through their own local parents before the root's real callers.
        // No static-composed closure result enters this queue.
        writes.forEachObservedId { id ->
            checkpoint()
            if (keys.row(id).original.base != STATIC) binding.offer(owner, id)
        }
        for (bridge in state.staticGuidanceSeeds.frozenRows()) {
            checkpoint()
            seed(owner, bridge.from, bridge.to)
        }
        for (terminal in state.outgoingTargets) {
            checkpoint()
            check(terminal.target == Target.DemandTarget)
            val original = checkNotNull(terminal.premise as? InitialAp) { "Run-1 cannot retain an ND original" }
            if (scope == BlockScope.ROOT) builder.addTarget(actor.key, original.toPattern())
            else builder.addScopedTarget(ScopedSummaryKey(actor.key, scope, PortId.ROOT_EXIT), original.toPattern())
        }
        val stores = if (scope == BlockScope.ROOT) sequenceOf(PortId.ROOT_EXIT to state.summaries)
            else state.portSummaries.entries()
        for ((exit, summaries) in stores) {
            if (scope != BlockScope.ROOT) builder.addScopedBoundary(ScopedSummaryKey(actor.key, scope, exit))
            for ((original, facts) in summaries.demandEdges(Direction.FORWARD)) {
                checkpoint()
                check(original is InitialAp) { "Run-1 cannot retain an ND original" }
                for (piece in shared.ops.leaves(facts)) {
                    checkpoint()
                    seed(owner, original.toPattern(), piece, exit)
                    if (piece.fact.base == STATIC && original.base != STATIC)
                        binding.offer(owner, keys.intern(original, piece))
                }
            }
        }
    }
    val writerStarted = TimeSource.Monotonic.markNow()
    val counters = binding.complete()
    val writerTime = writerStarted.elapsedNow()
    checkpoint()
    val freezeStarted = TimeSource.Monotonic.markNow()
    val frozen = builder.build()
    val freezeTime = freezeStarted.elapsedNow()
    checkpoint()
    return JoinedStaticGuidance(frozen, counters, observed, lost, peak, pruneTime, writerTime, freezeTime)
}
