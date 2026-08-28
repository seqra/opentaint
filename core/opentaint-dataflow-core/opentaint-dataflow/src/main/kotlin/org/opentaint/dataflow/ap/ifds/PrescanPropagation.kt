package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
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
    policy: PrescanPropagationPolicy = PrescanPropagationPolicy.None,
) {
    private val coordinator = PrescanSeedCoordinator(scopeMethods, policy)

    fun onNewSummaryStorage(
        storage: SummaryEdgeStorageWithSubscribers,
        manager: AnalysisUnitRunnerManager,
    ) {
        val source = storage.methodEntryPoint

        storage.subscribeOnEdges(object : SummaryEdgeStorageWithSubscribers.Subscriber {
            override fun newSummaryEdges(edges: List<Edge>) {
                val deliveries = coordinator.acceptSummaryEdges(source, edges)
                submitDeliveries(deliveries, manager)
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
        deliveries: List<PrescanSeedCoordinator.Delivery>,
        manager: AnalysisUnitRunnerManager,
    ) {
        for ((sourceMethod, methodEntryPoint, facts) in deliveries) {
            val sourceUnit = manager.unitResolver.resolve(sourceMethod)
            if (sourceUnit == UnknownUnit) continue
            facts.forEach { fact -> manager.handleCrossUnitFactCall(sourceUnit, methodEntryPoint, fact) }
        }
    }
}

class PrescanSeedCoordinator(
    scopeMethods: Collection<CommonMethod>,
    private val policy: PrescanPropagationPolicy,
) {
    data class Delivery(
        val sourceMethod: CommonMethod,
        val methodEntryPoint: MethodEntryPoint,
        val facts: List<FinalFactAp>,
    )

    data class Stats(
        val scopeMethods: Int,
        val targetEntryPoints: Int,
        val globalSeeds: Int,
        val constructorSeeds: Int,
        val globalDeliveries: Long,
        val constructorDeliveries: Long,
        val duplicates: Long,
        val largestGlobalSeedFanOut: Int,
        val largestOwner: PrescanInitializerOwner?,
        val largestOwnerSeedFanOut: Int,
    )

    private data class Target(
        val receiverOwner: PrescanInitializerOwner?,
    )

    private val scopeMethods = scopeMethods.toHashSet()
    private val targets = linkedMapOf<MethodEntryPoint, Target>()

    private val globalSeedSet = hashSetOf<FinalFactAp>()
    private val ownerSeedSets = hashMapOf<PrescanInitializerOwner, MutableSet<FinalFactAp>>()

    private var globalDeliveries = 0L
    private var constructorDeliveries = 0L
    private var duplicates = 0L

    init {
        for (method in this.scopeMethods) {
            val target = Target(policy.receiverOwner(method))
            for (entry in method.flowGraph().entries) {
                targets[MethodEntryPoint(EmptyMethodContext, entry)] = target
            }
        }
    }

    @Synchronized
    fun acceptSummaryEdges(
        source: MethodEntryPoint,
        edges: List<Edge>,
    ): List<Delivery> {
        if (edges.isEmpty()) return emptyList()

        val deliveries = linkedMapOf<MethodEntryPoint, MutableList<FinalFactAp>>()
        for (edge in edges) {
            if (edge !is Edge.ZeroToFact) continue

            when (edge.factAp.base) {
                AccessPathBase.ClassStatic -> addGlobalSeed(edge.factAp, deliveries)
                AccessPathBase.This -> {
                    if (source.method !in scopeMethods) continue
                    val owner = policy.initializerOwner(source.method) ?: continue
                    addOwnerSeed(owner, edge.factAp, deliveries)
                }
                else -> Unit
            }
        }

        return deliveries.map { (methodEntryPoint, facts) ->
            Delivery(source.method, methodEntryPoint, facts)
        }
    }

    @Synchronized
    fun stats(): Stats {
        val largestOwner = ownerSeedSets.keys.maxByOrNull { owner ->
            targets.values.count { it.receiverOwner == owner }
        }
        val largestOwnerFanOut = largestOwner?.let { owner ->
            targets.values.count { it.receiverOwner == owner }
        } ?: 0

        return Stats(
            scopeMethods = scopeMethods.size,
            targetEntryPoints = targets.size,
            globalSeeds = globalSeedSet.size,
            constructorSeeds = ownerSeedSets.values.sumOf { it.size },
            globalDeliveries = globalDeliveries,
            constructorDeliveries = constructorDeliveries,
            duplicates = duplicates,
            largestGlobalSeedFanOut = if (globalSeedSet.isEmpty()) 0 else targets.size,
            largestOwner = largestOwner,
            largestOwnerSeedFanOut = largestOwnerFanOut,
        )
    }

    private fun addGlobalSeed(
        fact: FinalFactAp,
        deliveries: MutableMap<MethodEntryPoint, MutableList<FinalFactAp>>,
    ) {
        if (!globalSeedSet.add(fact)) {
            duplicates++
            return
        }

        for (methodEntryPoint in targets.keys) {
            deliveries.getOrPut(methodEntryPoint, ::arrayListOf) += fact
            globalDeliveries++
        }
    }

    private fun addOwnerSeed(
        owner: PrescanInitializerOwner,
        fact: FinalFactAp,
        deliveries: MutableMap<MethodEntryPoint, MutableList<FinalFactAp>>,
    ) {
        val seedSet = ownerSeedSets.getOrPut(owner, ::hashSetOf)
        if (!seedSet.add(fact)) {
            duplicates++
            return
        }

        for ((methodEntryPoint, target) in targets) {
            if (target.receiverOwner != owner) continue
            deliveries.getOrPut(methodEntryPoint, ::arrayListOf) += fact
            constructorDeliveries++
        }
    }
}
