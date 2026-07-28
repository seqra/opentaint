package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

object MethodSummaryEdgeApplicationUtils {
    sealed interface SummaryEdgeApplication {
        data class SummaryApRefinement(val delta: FinalFactAp.Delta) : SummaryEdgeApplication

        /**
         * The empty-delta application. [emptyDelta] carries the caller abstraction's excluded-mark
         * claim from the match point (tree mode); appliers concat it onto the summary's exit fact
         * so the claim survives the transit — the structural counterpart of this refinement
         * carrying the caller's exclusion set.
         */
        data class SummaryExclusionRefinement(
            val exclusion: ExclusionSet,
            val emptyDelta: FinalFactAp.Delta? = null,
        ) : SummaryEdgeApplication
    }

    fun tryApplySummaryEdge(
        methodInitialFactAp: FinalFactAp,
        methodSummaryInitialFactAp: InitialFactAp,
    ): List<SummaryEdgeApplication> =
        methodInitialFactAp.delta(methodSummaryInitialFactAp).map { delta ->
            if (delta.isEmpty) {
                SummaryEdgeApplication.SummaryExclusionRefinement(
                    methodInitialFactAp.exclusions.union(methodSummaryInitialFactAp.exclusions),
                    emptyDelta = delta,
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
