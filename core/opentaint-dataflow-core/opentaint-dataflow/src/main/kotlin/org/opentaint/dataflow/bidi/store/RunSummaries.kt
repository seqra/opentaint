package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import java.util.IdentityHashMap

/** Raw exit conclusions and selected publications are separate collections. */
class RunSummaryStore(private val m: ApManager, flowBacked: Boolean = false) {
    private val groups = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val demand = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val interners = m.newInterners()
    private val backed = if (flowBacked) FlowBackedSummaries(m) else null
    private val backedDemand = if (flowBacked) FlowBackedSummaries(m) else null

    /** Raw delta. R1 persistence reads this collection at the barrier. */
    fun add(premise: PremiseKey, g: Facts): Facts? {
        m.cancellation.checkpoint()
        checkShape(premise, g)
        backed?.let { return it.add(premise, g) }
        return groups.getOrPut(premise) { ConclusionGroup(m, interners) }.add(g)
    }

    /** Publication delta. The caller has selected the raw group before restriction. */
    fun addDemand(premise: PremiseKey, piece: Facts): Facts? {
        m.cancellation.checkpoint()
        checkShape(premise, piece)
        backedDemand?.let { return it.add(premise, piece) }
        return demand.getOrPut(premise) { ConclusionGroup(m, interners) }.add(piece)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = backed?.all() ?: entries(groups)
    fun demandEdges(): Sequence<Pair<PremiseKey, Facts>> = backedDemand?.all() ?: entries(demand)

    /** Raw owner only. Demand publication state has a separate census, so a
     * caller cannot accidentally count both collections as one relation. */
    fun census(): RelationCensus = backed?.census() ?: census(groups)
    fun demandCensus(): RelationCensus = backedDemand?.census() ?: census(demand)

    private fun census(source: IdentityHashMap<PremiseKey, ConclusionGroup>): RelationCensus {
        m.cancellation.checkpoint()
        val counter = RelationCensusCounter(m.cancellation)
        var result = RelationCensus.ZERO
        for (group in source.values) for (facts in group.all()) {
            m.cancellation.checkpoint()
            result += counter.scalar(facts)
        }
        return result
    }

    /** Borrow the current raw relation on its actor owner. Consume this view
     * before mutating the store; do not retain a historical Facts snapshot. */
    fun borrow(premise: PremiseKey): Sequence<Facts> {
        m.cancellation.checkpoint()
        return backed?.borrow(premise) ?: groups[premise]?.all() ?: emptySequence()
    }

    private fun checkShape(premise: PremiseKey, facts: Facts) {
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
