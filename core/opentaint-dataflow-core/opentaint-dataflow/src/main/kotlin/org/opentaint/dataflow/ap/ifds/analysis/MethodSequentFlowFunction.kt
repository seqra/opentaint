package org.opentaint.dataflow.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils
import org.opentaint.dataflow.ap.ifds.MethodSummaryEdgeApplicationUtils.SummaryEdgeApplication
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem

interface MethodSequentFlowFunction {
    sealed interface Sequent {
        data object Unchanged : Sequent
        data object ZeroToZero : Sequent

        data class ZeroToFact(val factAp: FinalFactAp, val traceInfo: TraceInfo?) : Sequent
        data class FactToFact(val initialFactAp: InitialFactAp, val factAp: FinalFactAp, val traceInfo: TraceInfo?) : Sequent
        data class NDFactToFact(val initialFacts: Set<InitialFactAp>, val factAp: FinalFactAp, val traceInfo: TraceInfo?) : Sequent

        data class SideEffectRequirement(val initialFactAp: InitialFactAp) : Sequent

        sealed interface SideEffect : Sequent
        data class ZeroSideEffect(val kind: SideEffectKind) : SideEffect
        data class FactSideEffect(val initialFactAp: InitialFactAp, val kind: SideEffectKind) : SideEffect
    }

    sealed interface TraceInfo {
        data object Flow : TraceInfo
        data object ApplySummary : TraceInfo
        data class Rule(val rule: CommonTaintConfigurationItem, val action: CommonTaintAction): TraceInfo
    }

    fun propagateZeroToZero(): Set<Sequent>
    fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent>
    fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp): Set<Sequent>
    fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp): Set<Sequent>

    fun transfer(
        summary: StatementSummary,
        fact: FinalFactAp,
        typeChecker: FactTypeChecker,
        propagateFact: (FinalFactAp) -> Unit,
        refineInitial: (ExclusionSet) -> Unit,
    ): Boolean {
        val transfer = summary.find(fact.base) ?: return false

        var filtered = fact
        for (type in transfer.typeFilters) {
            filtered = typeChecker.filterFactByLocalType(type, filtered) ?: return true
        }

        for (edge in transfer.edges) {
            val to = edge.to
            for (effect in MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(filtered, edge.from)) {
                when (effect) {
                    is SummaryEdgeApplication.SummaryApRefinement -> {
                        if (to == null) continue
                        val result = to.concat(typeChecker, effect.delta) ?: continue
                        propagateFact(result.replaceExclusions(filtered.exclusions))
                    }

                    is SummaryEdgeApplication.SummaryExclusionRefinement -> {
                        if (to == null) {
                            refineInitial(effect.exclusion)
                            continue
                        }
                        val result = to.concat(typeChecker, effect.delta) ?: continue
                        propagateFact(result.replaceExclusions(effect.exclusion))
                    }
                }
            }
        }

        return true
    }
}