package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.FrozenCompletion
import org.opentaint.dataflow.bidi.store.FrozenStaticCompletion
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
    val binding = JoinedStaticWriterBinding(shared.ops, config.mode, keys,
        borrow = { method, writer, visit -> storage(method)?.visitJoinedInputs(writer, config.mode, visit) },
        onBound = { method, original, output -> builder.addSeed(method, original.toPattern(), output) },
        checkpoint = checkpoint)
    var observed = 0L
    var lost = 0L
    var peak = 0L
    var pruneTime = Duration.ZERO
    for (actor in actors) {
        checkpoint()
        val pruneStarted = TimeSource.Monotonic.markNow()
        val writes = actor.freezeStaticWriteCandidates()
        pruneTime += pruneStarted.elapsedNow()
        observed += writes.observedCount
        lost += writes.lostCount
        peak += writes.peakCount
        writes.forEachLostId { id ->
            checkpoint()
            val row = keys.row(id)
            builder.addSeed(actor.key, row.original.toPattern(), row.result)
        }
        // All primitive observed writers can expose a dependency at a caller.
        // They are not static-composed closure rows. B never enters BIND-W.
        writes.forEachObservedId { id ->
            checkpoint()
            if (keys.row(id).original.base != STATIC) binding.offer(actor.key, id)
        }
        for (bridge in actor.staticGuidanceSeeds.frozenRows()) {
            checkpoint()
            builder.addSeed(actor.key, bridge)
        }
        for ((original, facts) in actor.summaries.demandEdges()) {
            checkpoint()
            check(original is InitialAp) { "Run-1 cannot retain an ND original" }
            for (piece in shared.ops.leaves(facts)) {
                checkpoint()
                builder.addSeed(actor.key, original.toPattern(), piece)
                if (piece.fact.base == STATIC && original.base != STATIC)
                    binding.offer(actor.key, keys.intern(original, piece))
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
