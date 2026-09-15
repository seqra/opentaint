package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

object MethodSummaryEdgeApplicationUtils {
    sealed interface EdgeRefinement {
        data object UniverseRefinement : EdgeRefinement
        data object IdRefinement : EdgeRefinement
        data class ForcedRefinement(val requiredExclusions: ExclusionSet) : EdgeRefinement
    }

    sealed interface SummaryEdgeApplication: EdgeRefinement {
        val delta: FinalFactAp.Delta

        data class SummaryApRefinement(override val delta: FinalFactAp.Delta) : SummaryEdgeApplication
        data class SummaryExclusionRefinement(override val delta: FinalFactAp.Delta, val exclusion: ExclusionSet) : SummaryEdgeApplication
    }

    fun tryApplySummaryEdge(
        methodInitialFactAp: FinalFactAp,
        methodSummaryInitialFactAp: InitialFactAp,
    ): List<SummaryEdgeApplication> =
        methodInitialFactAp.delta(methodSummaryInitialFactAp).map { delta ->
            if (delta.isEmpty) {
                SummaryEdgeApplication.SummaryExclusionRefinement(
                    delta,
                    methodInitialFactAp.exclusions.union(methodSummaryInitialFactAp.exclusions)
                )
            } else {
                SummaryEdgeApplication.SummaryApRefinement(delta)
            }
        }

    fun emptyDeltaExclusionRefinementOrNull(
        methodInitialFactAp: FinalFactAp,
        methodSummaryInitialFactAp: InitialFactAp,
    ): ExclusionSet? {
        if (methodInitialFactAp.hasEmptyDelta(methodSummaryInitialFactAp)) {
            return methodSummaryInitialFactAp.exclusions
        }
        return null
    }
}
