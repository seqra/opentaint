package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.ExactDemandResults
import org.opentaint.dataflow.bidi.store.BlockScope
import java.util.Collections

/** A frozen query result. R contains the complete scoped/port-labelled enclosing result key.
 *
 * The observer must include all three families. A successful first family is not permission to
 * stop the query. It must not execute rules, subscriptions, source hooks or static effects.
 */
internal class LoopObservation<R>(
    adjacentInitials: Collection<AdmittedInitial>,
    enclosingResults: Collection<R>,
    repeatInitials: Collection<AdmittedInitial>,
    labelledAdmissions: Collection<LoopLabelledAdmission> = emptyList(),
) {
    val adjacentInitials: Set<AdmittedInitial> = frozenSet(adjacentInitials)
    val enclosingResults: Set<R> = frozenSet(enclosingResults)
    val repeatInitials: Set<AdmittedInitial> = frozenSet(repeatInitials)
    val labelledAdmissions: Set<LoopLabelledAdmission> = frozenSet(labelledAdmissions)
    val isEmpty: Boolean get() = adjacentInitials.isEmpty() && enclosingResults.isEmpty() && repeatInitials.isEmpty() &&
        labelledAdmissions.isEmpty()

    override fun equals(other: Any?): Boolean = this === other || other is LoopObservation<*> &&
        adjacentInitials == other.adjacentInitials && enclosingResults == other.enclosingResults &&
        repeatInitials == other.repeatInitials && labelledAdmissions == other.labelledAdmissions

    override fun hashCode(): Int = ((adjacentInitials.hashCode() * 31 + enclosingResults.hashCode()) * 31 +
        repeatInitials.hashCode()) * 31 + labelledAdmissions.hashCode()
}

internal enum class LoopAdmissionFamily { ADJACENT, REPEAT }
internal data class LoopLabelledAdmission(val scope: BlockScope, val family: LoopAdmissionFamily,
                                         val admitted: AdmittedInitial)

private fun <T> frozenSet(values: Collection<T>): Set<T> =
    Collections.unmodifiableSet(LinkedHashSet(values))

/** Exact geometry and annotation. Facts.equals intentionally omits the protection annotation. */
internal data class LoopObservedMember(val pattern: Pattern, val layer: Layer, val nonSubsumable: Boolean)

/** Query-local exact union. A protected copy wins over an otherwise identical plain copy. */
internal class LoopObservedFacts(private val ops: ApOps) {
    private data class Key(val pattern: Pattern, val layer: Layer)
    private val members = LinkedHashMap<Key, Boolean>()

    fun add(facts: Facts) {
        for (scalar in annotatedLoopScalars(ops, facts)) {
            ops.manager.cancellation.checkpoint()
            val pattern = ops.leaves(scalar).single()
            val key = Key(pattern, scalar.layer)
            members[key] = members[key] == true || scalar is TaintTree && scalar.nonSubsumable != null
        }
    }

    fun freeze(): Set<LoopObservedMember> = frozenSet(members.map { (key, protected) ->
        LoopObservedMember(key.pattern, key.layer, protected)
    })
}

/** Scalar output memberships with each exact protection coordinate retained before observing it. */
internal fun annotatedLoopScalars(ops: ApOps, packet: Facts): Sequence<Facts> = sequence {
    val ap = ops.manager
    if (packet is Reach) {
        ap.cancellation.checkpoint()
        yield(packet)
        return@sequence
    }
    for (leaf in ops.leaves(packet)) {
        ap.cancellation.checkpoint()
        val plain = ap.factsOf(leaf.fact, leaf.exclusion, packet.layer)
        yield(if (packet is TaintTree && plain is TaintTree)
            plain.withProtection(packet.nonSubsumable, ap.cancellation) else plain)
    }
}

/** Counts stored summary geometry, before a caller suffix is applied. ZERO has depth zero. */
internal fun loopFieldLength(premise: InitialAp): Int =
    if (premise.isZero) 0 else premise.path?.counted ?: 0

internal fun loopFieldLength(conclusion: Pattern): Int =
    conclusion.fact.path.count { it.isCounted() }

/** ND arms are restriction metadata only. The complete execution must have finished already. */
internal fun loopSummaryGrows(premise: PremiseKey, scalarConclusion: Pattern): Boolean {
    val outputDepth = loopFieldLength(scalarConclusion)
    premise.forEachMember { if (outputDepth <= loopFieldLength(it)) return false }
    return true
}

internal class LoopRestrictionStatistics {
    var offers: Long = 0; internal set
    var bypasses: Long = 0; internal set
    var scalarQueries: Long = 0; internal set
    var observations: Long = 0; internal set
    var trials: Long = 0; internal set
    var drops: Long = 0; internal set
    var cuts: Long = 0; internal set
    var rawFallbacks: Long = 0; internal set
}

/** Conservative shortest-safe-prefix reference from the selected loop specification.
 *
 * A call is for one stored output geometry, not an arbitrary packed summary. Applied values may
 * still contain several suffix/mark memberships; observe and cut those independently. The caller
 * captures the complete enclosing original, actual output port and immutable scope views in
 * [observe]. Restriction neither rewrites that context nor publishes a result.
 */
internal class LoopOutputRestriction(private val ops: ApOps) {
    val statistics = LoopRestrictionStatistics()

    fun <R> restrict(
        run1: Boolean,
        rowPremise: PremiseKey,
        scalarConclusion: Pattern,
        appliedValue: Facts,
        observe: (Facts) -> LoopObservation<R>,
    ): List<Facts> = restrict(run1, loopSummaryGrows(rowPremise, scalarConclusion), appliedValue, observe)

    /** Native reverse views keep a transient Pattern premise; classify that stored geometry
     * directly rather than interning a query-only MUST initial merely to call the gate. */
    fun <R> restrict(
        run1: Boolean,
        grows: Boolean,
        appliedValue: Facts,
        observe: (Facts) -> LoopObservation<R>,
    ): List<Facts> {
        val ap = ops.manager
        ap.cancellation.checkpoint()
        statistics.offers++
        if (run1 || appliedValue is Reach || !grows) {
            statistics.bypasses++
            return listOf(appliedValue)
        }
        val result = ExactDemandResults(ap)
        for (scalar in annotatedLoopScalars(ops, appliedValue)) {
            restrictScalar(scalar, observe)?.let(result::add)
        }
        return result.all()
    }

    private fun <R> restrictScalar(raw: Facts, observe: (Facts) -> LoopObservation<R>): Facts? {
        ops.manager.cancellation.checkpoint()
        statistics.scalarQueries++
        statistics.observations++
        val baseline = observe(raw)
        if (baseline.isEmpty) {
            statistics.drops++
            return null
        }
        val depth = when (raw) {
            is Reach -> 0
            is FlowTree -> raw.root.boundedDepth
            is TaintTree -> raw.root.boundedDepth
        }
        for (budget in 1 until depth) {
            ops.manager.cancellation.checkpoint()
            statistics.trials++
            var candidate: Facts? = null
            ops.limit(raw, budget, object : ApOut {
                override fun result(f: Facts) {
                    check(candidate == null) { "A scalar proper-prefix limit must have one output" }
                    candidate = f
                }

                override fun markRequest(mark: TaintMark) = error("A loop prefix cut cannot request a mark")
            })
            val cut = checkNotNull(candidate) { "A scalar field limit must have an output" }
            statistics.observations++
            if (observe(cut) == baseline) {
                check(cut.layer == Layer.DEMAND) { "A proper loop prefix cut must be DEMAND" }
                statistics.cuts++
                return cut
            }
        }
        statistics.rawFallbacks++
        return raw
    }
}
