package org.opentaint.dataflow.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.SideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.ExclusionSet
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
        Sequent.FactSideEffect(currentInitialFactAp.replaceExclusions(ex), k)
    }

    fun handleSummary(
        summaryEffect: SummaryEdgeApplication,
        kind: SideEffectKind,
        handleSE: (initialFactRefinement: ExclusionSet, kind: SideEffectKind) -> Sequent
    ): Set<Sequent> {
        // A side effect whose match needs a more concrete access path is not applicable yet.
        val exclusions = summaryEffect.initialFactExclusions ?: return emptySet()
        return setOf(handleSE(exclusions, kind))
    }
}
