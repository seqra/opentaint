package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.ir.api.common.CommonMethod

@JvmInline
value class PrescanInitializerOwner(val id: String)

interface PrescanPropagationPolicy {
    fun initializerOwner(method: CommonMethod): PrescanInitializerOwner? = null
    fun receiverOwner(method: CommonMethod): PrescanInitializerOwner? = null

    data object None : PrescanPropagationPolicy
}

class PrescanPropagationTargetResolver(
    scopeMethods: Collection<CommonMethod>,
    entrypointResolver: MethodEntrypointResolver,
    private val policy: PrescanPropagationPolicy = PrescanPropagationPolicy.None,
) {
    private val scopeMethods = scopeMethods.toSet()
    private val deliveryTargets: List<MethodEntryPoint>
    private val deliveryTargetsByOwner: Map<PrescanInitializerOwner, List<MethodEntryPoint>>

    init {
        val allTargets = arrayListOf<MethodEntryPoint>()
        val targetsByOwner = hashMapOf<PrescanInitializerOwner, MutableList<MethodEntryPoint>>()

        for (method in this.scopeMethods) {
            val methodTargets = entrypointResolver.resolveEntryPoints(method, EmptyMethodContext).map { entryPoint ->
                MethodEntryPoint(EmptyMethodContext, entryPoint)
            }
            allTargets += methodTargets

            val owner = policy.receiverOwner(method) ?: continue
            targetsByOwner.getOrPut(owner, ::arrayListOf) += methodTargets
        }

        deliveryTargets = allTargets
        deliveryTargetsByOwner = targetsByOwner
    }

    fun resolve(
        source: MethodEntryPoint,
        fact: FinalFactAp,
    ): List<MethodEntryPoint> {
        return when (fact.base) {
            AccessPathBase.ClassStatic -> deliveryTargets
            AccessPathBase.This -> {
                if (source.method !in scopeMethods) return emptyList()
                val owner = policy.initializerOwner(source.method) ?: return emptyList()
                deliveryTargetsByOwner[owner].orEmpty()
            }
            else -> emptyList()
        }
    }
}
