package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.excludeField

sealed class JIRSequentEdge(
    private val sequents: MutableSet<Sequent>,
    val current: FinalFactAp,
) {
    abstract val initialFacts: Set<InitialFactAp>

    fun add(sequent: Sequent) {
        sequents.add(sequent)
    }

    fun unchanged() = add(Sequent.Unchanged)

    fun propagate(fact: FinalFactAp) = add(edge(fact, TraceInfo.Flow))

    abstract fun propagateRefined(refinement: ExclusionSet, fact: FinalFactAp, trace: TraceInfo = TraceInfo.Flow)

    abstract fun propagateExcluded(fact: FinalFactAp, accessor: Accessor)

    abstract fun requireRefinement(refinement: ExclusionSet)

    protected abstract fun edge(fact: FinalFactAp, trace: TraceInfo): Sequent

    class ZeroToFact(sequents: MutableSet<Sequent>, current: FinalFactAp) :
        Unrefinable(sequents, current, "Zero to Fact") {
        override val initialFacts: Set<InitialFactAp> get() = emptySet()

        override fun edge(fact: FinalFactAp, trace: TraceInfo) = Sequent.ZeroToFact(fact, trace)
    }

    class NDFactToFact(
        sequents: MutableSet<Sequent>,
        override val initialFacts: Set<InitialFactAp>,
        current: FinalFactAp,
    ) : Unrefinable(sequents, current, "NDF2F") {
        override fun edge(fact: FinalFactAp, trace: TraceInfo) = Sequent.NDFactToFact(initialFacts, fact, trace)
    }

    class FactToFact(
        sequents: MutableSet<Sequent>,
        val initialFact: InitialFactAp,
        current: FinalFactAp,
    ) : JIRSequentEdge(sequents, current) {
        override val initialFacts: Set<InitialFactAp> get() = setOf(initialFact)

        override fun edge(fact: FinalFactAp, trace: TraceInfo) = Sequent.FactToFact(initialFact, fact, trace)

        override fun propagateRefined(refinement: ExclusionSet, fact: FinalFactAp, trace: TraceInfo) {
            add(Sequent.FactToFact(initialFact.refine(refinement), fact.refine(refinement), trace))
        }

        override fun propagateExcluded(fact: FinalFactAp, accessor: Accessor) {
            add(Sequent.FactToFact(initialFact.excludeField(accessor), fact.excludeField(accessor), TraceInfo.Flow))
        }

        override fun requireRefinement(refinement: ExclusionSet) {
            add(Sequent.SideEffectRequirement(initialFact.replaceExclusions(ExclusionSet.Empty).refine(refinement)))
        }
    }

    sealed class Unrefinable(
        sequents: MutableSet<Sequent>,
        current: FinalFactAp,
        private val kind: String,
    ) : JIRSequentEdge(sequents, current) {
        override fun propagateRefined(refinement: ExclusionSet, fact: FinalFactAp, trace: TraceInfo) {
            requireRefinement(refinement)
            add(edge(fact, trace))
        }

        override fun propagateExcluded(fact: FinalFactAp, accessor: Accessor) {
            error("$kind edge can't be refined: $current")
        }

        override fun requireRefinement(refinement: ExclusionSet) {
            check(refinement is ExclusionSet.Empty) { "$kind edge can't be refined: $current" }
        }
    }

    companion object {
        private fun InitialFactAp.refine(refinement: ExclusionSet): InitialFactAp =
            if (refinement is ExclusionSet.Empty) this else replaceExclusions(exclusions.union(refinement))

        private fun FinalFactAp.refine(refinement: ExclusionSet): FinalFactAp =
            if (refinement is ExclusionSet.Empty) this else replaceExclusions(exclusions.union(refinement))
    }
}
