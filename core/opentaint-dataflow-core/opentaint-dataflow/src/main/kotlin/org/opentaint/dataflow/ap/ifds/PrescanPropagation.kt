package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.ir.api.common.CommonMethod

@JvmInline
value class PrescanInitializerOwner(val id: String)

interface PrescanPropagationPolicy {
    fun initializerOwner(method: CommonMethod): PrescanInitializerOwner? = null
    fun receiverOwner(method: CommonMethod): PrescanInitializerOwner? = null

    data object None : PrescanPropagationPolicy
}

class PrescanSeedCoordinator(
    scopeMethods: Collection<CommonMethod>,
    private val policy: PrescanPropagationPolicy,
) {
    data class Delivery(
        val methodEntryPoint: MethodEntryPoint,
        val facts: List<FinalFactAp>,
    )

    data class Stats(
        val scopeMethods: Int,
        val activeEntryPoints: Int,
        val globalSeeds: Int,
        val constructorSeeds: Int,
        val globalDeliveries: Long,
        val constructorDeliveries: Long,
        val duplicates: Long,
        val replayedEntryPoints: Long,
        val largestGlobalSeedFanOut: Int,
        val largestOwner: PrescanInitializerOwner?,
        val largestOwnerSeedFanOut: Int,
    )

    private data class ActiveTarget(
        val receiverOwner: PrescanInitializerOwner?,
    )

    private val scopeMethods = scopeMethods.toHashSet()
    private val activeTargets = linkedMapOf<MethodEntryPoint, ActiveTarget>()

    private val globalSeeds = arrayListOf<FinalFactAp>()
    private val globalSeedSet = hashSetOf<FinalFactAp>()
    private val globalVersions = hashMapOf<MethodEntryPoint, Int>()

    private val ownerSeeds = hashMapOf<PrescanInitializerOwner, MutableList<FinalFactAp>>()
    private val ownerSeedSets = hashMapOf<PrescanInitializerOwner, MutableSet<FinalFactAp>>()
    private val ownerVersions = hashMapOf<MethodEntryPoint, Int>()

    private var globalDeliveries = 0L
    private var constructorDeliveries = 0L
    private var duplicates = 0L
    private var replayedEntryPoints = 0L

    @Synchronized
    fun activate(methodEntryPoint: MethodEntryPoint): List<Delivery> {
        val method = methodEntryPoint.method
        if (method !in scopeMethods) return emptyList()
        if (activeTargets.containsKey(methodEntryPoint)) return emptyList()

        val target = ActiveTarget(policy.receiverOwner(method))
        activeTargets[methodEntryPoint] = target

        val facts = arrayListOf<FinalFactAp>()

        val globalStart = globalVersions[methodEntryPoint] ?: 0
        if (globalStart < globalSeeds.size) {
            facts += globalSeeds.subList(globalStart, globalSeeds.size)
            globalDeliveries += globalSeeds.size - globalStart
        }
        globalVersions[methodEntryPoint] = globalSeeds.size

        val receiverOwner = target.receiverOwner
        if (receiverOwner != null) {
            val seeds = ownerSeeds[receiverOwner].orEmpty()
            val ownerStart = ownerVersions[methodEntryPoint] ?: 0
            if (ownerStart < seeds.size) {
                facts += seeds.subList(ownerStart, seeds.size)
                constructorDeliveries += seeds.size - ownerStart
            }
            ownerVersions[methodEntryPoint] = seeds.size
        }

        if (facts.isEmpty()) return emptyList()
        replayedEntryPoints++
        return listOf(Delivery(methodEntryPoint, facts))
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

        return deliveries.map { (methodEntryPoint, facts) -> Delivery(methodEntryPoint, facts) }
    }

    @Synchronized
    fun stats(): Stats {
        val largestOwner = ownerSeeds.keys.maxByOrNull { owner ->
            activeTargets.values.count { it.receiverOwner == owner }
        }
        val largestOwnerFanOut = largestOwner?.let { owner ->
            activeTargets.values.count { it.receiverOwner == owner }
        } ?: 0

        return Stats(
            scopeMethods = scopeMethods.size,
            activeEntryPoints = activeTargets.size,
            globalSeeds = globalSeeds.size,
            constructorSeeds = ownerSeeds.values.sumOf { it.size },
            globalDeliveries = globalDeliveries,
            constructorDeliveries = constructorDeliveries,
            duplicates = duplicates,
            replayedEntryPoints = replayedEntryPoints,
            largestGlobalSeedFanOut = if (globalSeeds.isEmpty()) 0 else activeTargets.size,
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

        globalSeeds += fact
        val version = globalSeeds.size
        for (methodEntryPoint in activeTargets.keys) {
            deliveries.getOrPut(methodEntryPoint, ::arrayListOf) += fact
            globalVersions[methodEntryPoint] = version
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

        val seeds = ownerSeeds.getOrPut(owner, ::arrayListOf)
        seeds += fact
        val version = seeds.size
        for ((methodEntryPoint, target) in activeTargets) {
            if (target.receiverOwner != owner) continue
            deliveries.getOrPut(methodEntryPoint, ::arrayListOf) += fact
            ownerVersions[methodEntryPoint] = version
            constructorDeliveries++
        }
    }
}
