package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.IdentityHashMap

/** One admitted relation. Outgoing demand is a filtered view of the final stored headers. */
class RunSummaryStore(private val m: ApManager, flowBacked: Boolean = false) {
    private val groups = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val interners = m.newInterners()
    private val backed = if (flowBacked) FlowBackedSummaries(m) else null

    /** Add a candidate only after the actor has completed demand restriction. */
    fun addAdmitted(premise: PremiseKey, g: Facts): Facts? {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, g)) return null
        checkShape(premise, g)
        backed?.let { return it.add(premise, g) }
        return groups.getOrPut(premise) { ConclusionGroup(m, interners) }.add(g)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = backed?.all() ?: entries(groups)

    fun demandEdges(direction: Direction): Sequence<Pair<PremiseKey, Facts>> =
        all().filter { (premise, facts) -> selectedForHandoff(premise, facts.layer, direction) }

    fun census(): RelationCensus = census { _, _ -> true }

    fun demandCensus(direction: Direction): RelationCensus =
        census { premise, layer -> selectedForHandoff(premise, layer, direction) }

    private fun census(include: (PremiseKey, Layer) -> Boolean): RelationCensus {
        m.cancellation.checkpoint()
        backed?.let { return it.census(include) }
        val counter = RelationCensusCounter(m.cancellation)
        var result = RelationCensus.ZERO
        for ((premise, group) in groups) for (facts in group.all()) {
            m.cancellation.checkpoint()
            if (include(premise, facts.layer)) result += counter.scalar(facts)
        }
        return result
    }

    /** Borrow the current admitted relation on its actor owner. Consume this view
     * before mutating the store; do not retain a historical Facts snapshot. */
    fun borrow(premise: PremiseKey): Sequence<Facts> {
        m.cancellation.checkpoint()
        return backed?.borrow(premise) ?: groups[premise]?.all() ?: emptySequence()
    }

    private fun checkShape(premise: PremiseKey, facts: Facts) {
        assertCanonicalFlowSummary(premise, facts)
        check(facts.base !is AccessPathBase.CleanerTemporary) { "A field-action temporary cannot enter a summary" }
        check((facts is FlowTree) == premise.isFlow) { "K6: the conclusion kind follows the premise" }
        check(premise !is PremiseSet || facts is TaintTree) { "A multi-premise summary must be TAINT" }
    }

    private fun entries(source: IdentityHashMap<PremiseKey, ConclusionGroup>): Sequence<Pair<PremiseKey, Facts>> = sequence {
        m.cancellation.checkpoint()
        for ((premise, group) in source) {
            m.cancellation.checkpoint()
            for (facts in group.all()) {
                m.cancellation.checkpoint()
                yield(premise to facts)
            }
        }
    }
}
