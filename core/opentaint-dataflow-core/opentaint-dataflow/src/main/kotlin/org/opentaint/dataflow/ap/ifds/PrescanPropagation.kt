package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ifds.UnknownUnit

class PrescanPropagation(
    private val targetResolver: PrescanPropagationTargetResolver,
) {
    fun onNewSummaryStorage(
        storage: SummaryEdgeStorageWithSubscribers,
        manager: AnalysisUnitRunnerManager,
    ) {
        val source = storage.methodEntryPoint

        storage.subscribeOnEdges(object : SummaryEdgeStorageWithSubscribers.Subscriber {
            override fun newSummaryEdges(edges: List<Edge>) {
                submitDeliveries(source, edges, manager)
            }

            override fun newSideEffectRequirement(
                methodEntryPoint: MethodEntryPoint,
                requirements: List<InitialFactAp>,
            ) = Unit

            override fun newSideEffectSummaries(
                methodEntryPoint: MethodEntryPoint,
                sideEffects: List<SideEffectSummary>,
            ) = Unit
        })
    }

    private fun submitDeliveries(
        source: MethodEntryPoint,
        edges: List<Edge>,
        manager: AnalysisUnitRunnerManager,
    ) {
        val sourceUnit = manager.unitResolver.resolve(source.method)
        if (sourceUnit == UnknownUnit) return

        for (edge in edges) {
            if (edge !is Edge.ZeroToFact) continue
            for (target in targetResolver.resolve(source, edge.factAp)) {
                manager.handleCrossUnitFactCall(sourceUnit, target, edge.factAp)
            }
        }
    }
}
