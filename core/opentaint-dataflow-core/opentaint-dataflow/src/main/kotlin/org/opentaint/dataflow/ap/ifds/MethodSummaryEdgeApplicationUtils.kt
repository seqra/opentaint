package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

object MethodSummaryEdgeApplicationUtils {
    /**
     * The two independent refinements selected while matching a summary edge.
     *
     * [accessDelta] belongs to the access-path representation. [initialFactExclusions] belongs to
     * demand analysis and is present only for an empty access delta. Synthetic ND applications
     * may supply only [initialFactExclusions].
     */
    data class SummaryEdgeApplication(
        val accessDelta: FinalFactAp.Delta?,
        val initialFactExclusions: ExclusionSet?,
    ) {
        init {
            require(accessDelta != null || initialFactExclusions != null)
        }
    }

    fun tryApplySummaryEdge(
        methodInitialFactAp: FinalFactAp,
        methodSummaryInitialFactAp: InitialFactAp,
    ): List<SummaryEdgeApplication> =
        methodInitialFactAp.delta(methodSummaryInitialFactAp).map { delta ->
            if (delta.isEmpty) {
                SummaryEdgeApplication(
                    accessDelta = delta,
                    initialFactExclusions =
                        methodInitialFactAp.exclusions.union(methodSummaryInitialFactAp.exclusions),
                )
            } else {
                SummaryEdgeApplication(
                    accessDelta = delta,
                    initialFactExclusions = null,
                )
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
