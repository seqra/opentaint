package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

object MethodSummaryEdgeApplicationUtils {
    sealed interface SummaryEdgeApplication {
        data class SummaryApRefinement(val delta: FinalFactAp.Delta) : SummaryEdgeApplication

        /**
         * Demand refinement selected by an empty access-path delta.
         *
         * [representationDelta] independently carries state attached to the caller's abstraction,
         * such as an any-field cleaner effect. Synthetic applications must pass `null` explicitly
         * because they have no caller-side representation state to transfer.
         */
        data class SummaryDemandRefinement(
            val demandState: FactDemandState,
            val representationDelta: FinalFactAp.Delta?,
        ) : SummaryEdgeApplication
    }

    fun tryApplySummaryEdge(
        methodInitialFactAp: FinalFactAp,
        methodSummaryInitialFactAp: InitialFactAp,
    ): List<SummaryEdgeApplication> =
        methodInitialFactAp.delta(methodSummaryInitialFactAp).map { delta ->
            if (delta.isEmpty) {
                SummaryEdgeApplication.SummaryDemandRefinement(
                    methodInitialFactAp.demandState then methodSummaryInitialFactAp.demandState,
                    representationDelta = delta,
                )
            } else {
                SummaryEdgeApplication.SummaryApRefinement(delta)
            }
        }

    fun emptyDeltaDemandExclusionsOrNull(
        methodInitialFactAp: FinalFactAp,
        methodSummaryInitialFactAp: InitialFactAp,
    ): ExclusionSet? {
        if (methodInitialFactAp.hasEmptyDelta(methodSummaryInitialFactAp)) {
            return methodSummaryInitialFactAp.exclusions
        }
        return null
    }
}
