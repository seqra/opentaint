package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.api.common.CommonMethod

@JvmInline
value class PrescanInitializerOwner(val id: String)

interface PrescanPropagationPolicy {
    fun initializerOwner(method: CommonMethod): PrescanInitializerOwner? = null
    fun receiverOwner(method: CommonMethod): PrescanInitializerOwner? = null

    data object None : PrescanPropagationPolicy
}

class PrescanPropagation(
    scopeMethods: Collection<CommonMethod>,
    entrypointResolver: MethodEntrypointResolver,
    private val policy: PrescanPropagationPolicy = PrescanPropagationPolicy.None,
) {
    private data class DeliveryTarget(
        val entryPoint: MethodEntryPoint,
        val owner: PrescanInitializerOwner?,
    )

    private val scopeMethods = scopeMethods.toSet()
    private val deliveryTargets = this.scopeMethods.flatMap { method ->
        val owner = policy.receiverOwner(method)
        entrypointResolver.resolveEntryPoints(method, EmptyMethodContext).map { entryPoint ->
            DeliveryTarget(
                MethodEntryPoint(EmptyMethodContext, entryPoint),
                owner,
            )
        }
    }
    private val deliveryTargetsByOwner = deliveryTargets
        .filter { it.owner != null }
        .groupBy { it.owner }

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
            val targets = when (edge.factAp.base) {
                AccessPathBase.ClassStatic -> deliveryTargets
                AccessPathBase.This -> {
                    if (source.method !in scopeMethods) continue
                    val owner = policy.initializerOwner(source.method) ?: continue
                    deliveryTargetsByOwner[owner].orEmpty()
                }
                else -> continue
            }

            for (target in targets) {
                manager.handleCrossUnitFactCall(sourceUnit, target.entryPoint, edge.factAp)
            }
        }
    }
}
