package org.opentaint.dataflow.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.EdgeRefinement
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication.SummaryApRefinement
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication.SummaryExclusionRefinement
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo

interface MethodCallSummaryHandler {
    val factTypeChecker: FactTypeChecker

    sealed interface SummaryEdge {
        val methodEntryPoint: MethodEntryPoint
        val final: FinalFactAp

        data class F2F(
            override val methodEntryPoint: MethodEntryPoint,
            val initial: InitialFactAp,
            override val final: FinalFactAp,
        ) : SummaryEdge

        data class NdF2F(
            override val methodEntryPoint: MethodEntryPoint,
            val initial: Set<InitialFactAp>,
            override val final: FinalFactAp,
        ) : SummaryEdge
    }

    fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp>

    fun handleZeroToZero(summaryFact: FinalFactAp?): Set<Sequent> {
        if (summaryFact == null) return setOf(Sequent.ZeroToZero)

        val summaryExitFacts = mapMethodExitToReturnFlowFact(summaryFact)
        return summaryExitFacts.mapTo(hashSetOf()) {
            Sequent.ZeroToFact(it, TraceInfo.ApplySummary)
        }
    }

    fun prepareZeroToFactSummary(summaryEdge: Edge.ZeroToFact): List<Edge.ZeroToFact> = listOf(summaryEdge)

    fun handleZeroToFact(
        currentFactAp: FinalFactAp,
        summaryEffect: EdgeRefinement,
        summaryEdge: SummaryEdge,
    ): Set<Sequent> = handleSummary(
        currentFactAp,
        summaryEffect,
        summaryEdge,
        createSideEffectRequirement = {
            check(it is ExclusionSet.Universe) { "Incorrect refinement" }
            null
        }
    ) { initialFactRefinement: ExclusionSet?, summaryFactAp ->
        check(initialFactRefinement == null || initialFactRefinement is ExclusionSet.Universe) {
            "Incorrect refinement"
        }

        Sequent.ZeroToFact(summaryFactAp, TraceInfo.ApplySummary)
    }

    fun handleFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        summaryEffect: EdgeRefinement,
        summaryEdge: SummaryEdge,
    ): Set<Sequent> = handleSummary(
        currentFactAp,
        summaryEffect,
        summaryEdge,
        createSideEffectRequirement = { refinement ->
            Sequent.SideEffectRequirement(initialFactAp.refine(refinement))
        }
    ) { initialFactRefinement: ExclusionSet?, summaryFactAp: FinalFactAp ->
        Sequent.FactToFact(initialFactAp.refine(initialFactRefinement), summaryFactAp, TraceInfo.ApplySummary)
    }

    fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> = listOf(summaryEdge)

    fun handleNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        summaryEffect: EdgeRefinement,
        summaryEdge: SummaryEdge,
    ): Set<Sequent> = handleSummary(
        currentFactAp,
        summaryEffect,
        summaryEdge,
        createSideEffectRequirement = {
            check(it is ExclusionSet.Universe) { "Incorrect refinement" }
            null
        }
    ) { initialFactRefinement: ExclusionSet?, summaryFactAp: FinalFactAp ->
        check(initialFactRefinement == null || initialFactRefinement is ExclusionSet.Universe) {
            "Incorrect refinement"
        }

        Sequent.NDFactToFact(
            initialFacts.mapTo(hashSetOf()) { it.refine(initialFactRefinement) },
            summaryFactAp,
            TraceInfo.ApplySummary
        )
    }

    fun prepareNDFactToFactSummary(summaryEdge: Edge.NDFactToFact): List<Edge.NDFactToFact> = listOf(summaryEdge)

    fun InitialFactAp.refine(exclusionSet: ExclusionSet?) =
        if (exclusionSet == null) this else replaceExclusions(exclusionSet)

    fun handleSummary(
        currentFactAp: FinalFactAp,
        summaryEffect: EdgeRefinement,
        summaryEdge: SummaryEdge,
        createSideEffectRequirement: (refinement: ExclusionSet) -> Sequent?,
        handleSummaryEdge: (initialFactRefinement: ExclusionSet?, summaryFactAp: FinalFactAp) -> Sequent
    ): Set<Sequent> {
        val mappedSummaryFacts = mapMethodExitToReturnFlowFact(summaryEdge.final)

        return when (summaryEffect) {
            is SummaryEdgeApplication -> mappedSummaryFacts.mapNotNullTo(hashSetOf()) { mappedSummaryFact ->
                val summaryFactAp = mappedSummaryFact
                    .concat(factTypeChecker, summaryEffect.delta)
                    ?: return@mapNotNullTo null

                when (summaryEffect) {
                    is SummaryApRefinement -> {
                        // todo: filter exclusions
                        val fact = summaryFactAp.replaceExclusions(currentFactAp.exclusions)
                        handleSummaryEdge(null, fact)
                    }

                    is SummaryExclusionRefinement -> {
                        val fact = summaryFactAp.replaceExclusions(summaryEffect.exclusion)
                        handleSummaryEdge(summaryEffect.exclusion, fact)
                    }
                }
            }

            is EdgeRefinement.UniverseRefinement -> mappedSummaryFacts.mapTo(hashSetOf()) {
                handleSummaryEdge(ExclusionSet.Universe, it.replaceExclusions(ExclusionSet.Universe))
            }

            is EdgeRefinement.IdRefinement -> mappedSummaryFacts.mapTo(hashSetOf()) {
                handleSummaryEdge(currentFactAp.exclusions, it.replaceExclusions(currentFactAp.exclusions))
            }
        }
    }
}
