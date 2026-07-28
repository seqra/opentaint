package org.opentaint.dataflow.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication.SummaryApRefinement
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication.SummaryExclusionRefinement
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.SideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent

interface MethodSideEffectSummaryHandler {
    fun handleZeroToZero(
        sideEffects: List<SideEffectSummary.ZeroSideEffectSummary>,
    ): Set<Sequent> = emptySet()

    fun handleZeroToFact(
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        kind: SideEffectKind
    ): Set<Sequent> = handleSummary(summaryEffect, kind) { _, k ->
        Sequent.ZeroSideEffect(k)
    }

    fun handleFactToFact(
        currentInitialFactAp: InitialFactAp,
        currentFactAp: FinalFactAp,
        summaryEffect: SummaryEdgeApplication,
        kind: SideEffectKind
    ): Set<Sequent> = handleSummary(summaryEffect, kind) { ex, k ->
        val refined = FactFlowState(
            ex.exclusions,
            currentInitialFactAp.deepCleanEffects then ex.deepCleanEffects,
        )
        Sequent.FactSideEffect(currentInitialFactAp.replaceFlowState(refined), k)
    }

    fun handleSummary(
        summaryEffect: SummaryEdgeApplication,
        kind: SideEffectKind,
        handleSE: (initialFactRefinement: FactFlowState, kind: SideEffectKind) -> Sequent
    ): Set<Sequent> = when (summaryEffect) {
        // Side effect requires more concrete fact
        is SummaryApRefinement -> emptySet()

        is SummaryExclusionRefinement -> {
            setOf(handleSE(summaryEffect.flowState, kind))
        }
    }
}
