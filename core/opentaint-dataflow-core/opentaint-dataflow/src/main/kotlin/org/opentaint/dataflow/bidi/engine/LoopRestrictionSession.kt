package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.AnyDemandCursor
import org.opentaint.dataflow.bidi.store.BlockScope

internal data class LoopPrecisionCursor(val scope: BlockScope, val family: LoopAdmissionFamily,
                                        val cursor: AnyDemandCursor)

/** One scalar query. A witness rejects early budgets; it never replaces the full observer. */
internal class LoopRestrictionSession<R>(
    private val ops: ApOps,
    private val policy: RestrictedInitialPolicy,
    val observe: (Facts) -> LoopObservation<R>,
    private val precision: (Pattern) -> List<LoopPrecisionCursor>?,
) {
    private data class Key(val scope: BlockScope, val family: LoopAdmissionFamily,
                           val pattern: Pattern, val layer: Layer)

    fun certifiedFirstBudget(raw: Facts, baseline: LoopObservation<R>): Int? {
        val actual = ops.leaves(raw).singleOrNull() ?: return null
        val path = actual.fact.path
        if (actual.fact.base == STATIC || path.size <= 1 || path.any { !it.isCounted() }) return null
        var active = precision(actual)?.filter { it.cursor.subtreeWitness() != null } ?: return null
        if (active.isEmpty()) return null
        var parent = active
        var boundary = 1
        for (index in path.indices) {
            ops.manager.cancellation.checkpoint()
            parent = active
            boundary = index + 1
            // The final proper cut is at depth-1. A witness there can reject every trial.
            if (boundary == path.size) break
            val next = active.mapNotNull { labelled -> labelled.cursor.follow(path[index])?.let {
                labelled.copy(cursor = it)
            } }
            if (next.isEmpty()) break
            active = next
        }
        if (boundary <= 1) return null
        val prefix = path.take(boundary - 1)
        val cut = Pattern(actual.fact.copy(path = prefix, tail = Tail.ANY), ExclusionSet.Empty)
        var baselineKeys: Set<Key>? = null
        for (labelled in parent) {
            ops.manager.cancellation.checkpoint()
            val witness = labelled.cursor.subtreeWitness() ?: continue
            if (witness.fact.tail != Tail.ANY || witness.exclusion != ExclusionSet.Empty ||
                witness.fact.path.any { !it.isCounted() } ||
                !witness.fact.path.startsWith(prefix)) continue
            val emitted = policy.emitAdmission(witness, cut, Layer.DEMAND) ?: continue
            // Every earlier MAY prefix has the same native rendered image for this witness.
            if (emitted.pattern.fact.path != witness.fact.path || emitted.pattern.fact.tail != Tail.ANY ||
                emitted.layer != Layer.DEMAND) continue
            val keys = baselineKeys ?: baseline.labelledAdmissions.mapTo(HashSet()) {
                Key(it.scope, it.family, it.admitted.initial.toPattern(), it.admitted.layer)
            }.also { baselineKeys = it }
            if (Key(labelled.scope, labelled.family, emitted.pattern, emitted.layer) !in keys) return boundary
        }
        return null
    }
}
