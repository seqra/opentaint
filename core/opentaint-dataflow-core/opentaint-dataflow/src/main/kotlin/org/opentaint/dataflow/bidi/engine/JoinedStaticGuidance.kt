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
    val byMethod = actors.associateBy { it.key }
    return completeFromSources(config, shared, actors.flatMap { it.detachJoinedStaticSources() },
        borrow = { owner, writer, visit ->
            if (owner.local == BlockScope.ROOT) storage(owner.method)?.visitJoinedInputs(writer, config.mode) {
                check(it.callee == owner.method)
                visit(OwnedWriterInput.call(it))
            } else byMethod[owner.method]?.forEachJoinedLocalInput(owner.local) { link, actual ->
                checkpoint(); check(link.child == owner.local)
                visit(OwnedWriterInput.local(owner.method, link, actual))
            }
        }, checkpoint = checkpoint)
}

internal fun completeJoinedStaticGuidance(
    config: RunConfig,
    shared: SharedObjects,
    sources: List<JoinedStaticSource>,
    inputs: JoinedBindingLease,
    checkpoint: () -> Unit,
): JoinedStaticGuidance = completeFromSources(config, shared, sources,
    borrow = { owner, writer, visit ->
        if (owner.local == BlockScope.ROOT) inputs.visitCallerInputs(owner.method, writer, config.mode) {
            check(it.callee == owner.method)
            visit(OwnedWriterInput.call(it))
        } else inputs.visitLocalInputs(owner) { link, actual ->
            checkpoint(); check(link.child == owner.local)
            visit(OwnedWriterInput.local(owner.method, link, actual))
        }
    }, checkpoint = checkpoint)

private fun completeFromSources(
    config: RunConfig,
    shared: SharedObjects,
    sources: List<JoinedStaticSource>,
    borrow: (OwnedScope, Publication, (OwnedWriterInput) -> Unit) -> Unit,
    checkpoint: () -> Unit,
): JoinedStaticGuidance {
    check(config.run1)
    val builder = FrozenStaticCompletion.Builder(shared.ap, shared.staticCallGraph)
    val keys = shared.staticWriteKeyInterner
    fun seed(owner: OwnedScope, original: Pattern, output: Pattern, exit: PortId = PortId.STATIC_SHORTCUT) {
        if (owner.local == BlockScope.ROOT) builder.addSeed(owner.method, original, output)
        else builder.addScopedSeed(ScopedSummaryKey(owner.method, owner.local, exit), original, output)
    }
    val binding = OwnedJoinedStaticWriterBinding(shared.ops, config.mode, keys,
        borrow = borrow,
        onBound = { owner, original, output -> seed(owner, original.toPattern(), output) },
        checkpoint = checkpoint)
    var observed = 0L
    var lost = 0L
    var peak = 0L
    var pruneTime = Duration.ZERO
    for (source in sources) {
        checkpoint()
        val owner = source.owner
        val scope = owner.local
        val shortcut = ScopedSummaryKey(owner.method, scope, PortId.STATIC_SHORTCUT)
        if (scope != BlockScope.ROOT) builder.addScopedBoundary(shortcut)
        val pruneStarted = TimeSource.Monotonic.markNow()
        val writes = source.freezeWrites()
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
        for (bridge in source.privateSeeds.frozenRows()) {
            checkpoint()
            seed(owner, bridge.from, bridge.to)
        }
        for (terminal in source.outgoingDemandTargets) {
            checkpoint()
            check(terminal.target == Target.DemandTarget)
            val original = checkNotNull(terminal.premise as? InitialAp) { "Run-1 cannot retain an ND original" }
            if (scope == BlockScope.ROOT) builder.addTarget(owner.method, original.toPattern())
            else builder.addScopedTarget(ScopedSummaryKey(owner.method, scope, PortId.ROOT_EXIT), original.toPattern())
        }
        val stores = source.exitStores()
        for ((exit, summaries) in stores) {
            if (scope != BlockScope.ROOT) builder.addScopedBoundary(ScopedSummaryKey(owner.method, scope, exit))
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
