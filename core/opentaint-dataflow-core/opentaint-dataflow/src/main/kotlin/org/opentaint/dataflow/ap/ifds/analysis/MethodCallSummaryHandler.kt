package org.opentaint.dataflow.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication.SummaryApRefinement
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication.SummaryExclusionRefinement
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo

interface MethodCallSummaryHandler {
    val factTypeChecker: FactTypeChecker

    sealed interface SummaryEdge {
        val final: FinalFactAp

        data class F2F(val initial: InitialFactAp, override val final: FinalFactAp) : SummaryEdge
        data class NdF2F(val initial: Set<InitialFactAp>, override val final: FinalFactAp) : SummaryEdge
    }

    fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp>

    fun handleZeroToZero(summaryFact: FinalFactAp?): Set<Sequent> {
        if (summaryFact == null) return setOf(Sequent.ZeroToZero)

        val summaryExitFacts = mapMethodExitToReturnFlowFact(summaryFact)
        return summaryExitFacts.mapTo(hashSetOf()) {
            Sequent.ZeroToFact(it, TraceInfo.ApplySummary)
        }
    }

    fun handleZeroToFact(
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        summaryEdge: SummaryEdge,
    ): Set<Sequent> = handleSummary(
        currentFactAp,
        summaryEffect,
        summaryEdge,
        createSideEffectRequirement = {
            check(it.exclusions is ExclusionSet.Universe) { "Incorrect refinement" }
            null
        }
    ) { initialFactRefinement: FactFlowState?, summaryFactAp ->
        check(initialFactRefinement == null || initialFactRefinement.exclusions is ExclusionSet.Universe) {
            "Incorrect refinement"
        }

        Sequent.ZeroToFact(summaryFactAp, TraceInfo.ApplySummary)
    }

    fun handleFactToFact(
        initialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        summaryEdge: SummaryEdge,
    ): Set<Sequent> = handleSummary(
        currentFactAp,
        summaryEffect,
        summaryEdge,
        createSideEffectRequirement = { refinement ->
            Sequent.SideEffectRequirement(initialFactAp.refine(refinement))
        }
    ) { initialFactRefinement: FactFlowState?, summaryFactAp: FinalFactAp ->
        Sequent.FactToFact(initialFactAp.refine(initialFactRefinement), summaryFactAp, TraceInfo.ApplySummary)
    }

    fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> = listOf(summaryEdge)

    fun handleNDFactToFact(
        initialFacts: Set<InitialFactAp>,
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        summaryEdge: SummaryEdge,
    ): Set<Sequent> = handleSummary(
        currentFactAp,
        summaryEffect,
        summaryEdge,
        createSideEffectRequirement = {
            check(it.exclusions is ExclusionSet.Universe) { "Incorrect refinement" }
            null
        }
    ) { initialFactRefinement: FactFlowState?, summaryFactAp: FinalFactAp ->
        check(initialFactRefinement == null || initialFactRefinement.exclusions is ExclusionSet.Universe) {
            "Incorrect refinement"
        }

        Sequent.NDFactToFact(
            initialFacts.mapTo(hashSetOf()) { it.refine(initialFactRefinement) },
            summaryFactAp,
            TraceInfo.ApplySummary
        )
    }

    fun prepareNDFactToFactSummary(summaryEdge: Edge.NDFactToFact): List<Edge.NDFactToFact> = listOf(summaryEdge)

    fun InitialFactAp.refine(flowState: FactFlowState?) = when {
        flowState == null -> this
        else -> replaceFlowState(
            FactFlowState(flowState.exclusions) then FactFlowState(
                ExclusionSet.Empty,
                deepCleanEffects then flowState.deepCleanEffects,
            )
        )
    }

    fun handleSummary(
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        summaryEdge: SummaryEdge,
        createSideEffectRequirement: (refinement: FactFlowState) -> Sequent?,
        handleSummaryEdge: (initialFactRefinement: FactFlowState?, summaryFactAp: FinalFactAp) -> Sequent
    ): Set<Sequent> {
        val mappedSummaryFacts = mapMethodExitToReturnFlowFact(summaryEdge.final)

        return when (summaryEffect) {
            is SummaryApRefinement -> mappedSummaryFacts.mapNotNullTo(hashSetOf()) { mappedSummaryFact ->
                val summaryFactAp = mappedSummaryFact
                    .concat(factTypeChecker, summaryEffect.delta)
                    ?.replaceFlowState(
                        FactFlowState(currentFactAp.exclusions) then FactFlowState(
                            ExclusionSet.Empty,
                            mappedSummaryFact.deepCleanEffects then
                                summaryEffect.delta.deepCleanEffects
                        )
                    )
                    ?: return@mapNotNullTo null

                handleSummaryEdge(summaryFactAp.flowState, summaryFactAp)
            }

            is SummaryExclusionRefinement -> mappedSummaryFacts.mapNotNullTo(hashSetOf()) { mappedSummaryFact ->
                // todo: filter exclusions
                // The empty delta carries the caller abstraction's excluded-mark claim; the
                // concat transfers it onto the exit fact's abstraction so the claim survives
                // the transit (tree mode; a no-op elsewhere).
                val summaryAccess = summaryEffect.emptyDelta
                    ?.let { mappedSummaryFact.concat(factTypeChecker, it) ?: return@mapNotNullTo null }
                    ?: mappedSummaryFact

                val summaryFactAp = summaryAccess.replaceFlowState(summaryEffect.flowState)

                handleSummaryEdge(summaryEffect.flowState, summaryFactAp)
            }
        }
    }
}
