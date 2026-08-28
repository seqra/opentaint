package org.opentaint.dataflow.ap.ifds

import mu.KotlinLogging
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.api.common.CommonMethod

private val logger = KotlinLogging.logger {}

@JvmInline
value class PrescanInitializerOwner(val id: String)

interface PrescanPropagationPolicy {
    fun initializerOwner(method: CommonMethod): PrescanInitializerOwner? = null
    fun receiverOwner(method: CommonMethod): PrescanInitializerOwner? = null

    data object None : PrescanPropagationPolicy
}

class PrescanPropagation(
    private val policy: PrescanPropagationPolicy = PrescanPropagationPolicy.None,
) {
    @Volatile
    private var coordinator: PrescanSeedCoordinator? = null
    private var scopeUnits: Int = 0

    fun start(
        scopeMethods: Collection<CommonMethod>,
        manager: AnalysisUnitRunnerManager,
    ) {
        check(coordinator == null) { "Prescan propagation is already active" }
        val newCoordinator = PrescanSeedCoordinator(scopeMethods, policy)
        val newScopeUnits = scopeMethods.asSequence()
            .map(manager.unitResolver::resolve)
            .filter { it != UnknownUnit }
            .distinct()
            .count()
        scopeUnits = newScopeUnits
        coordinator = newCoordinator
    }

    fun finish() {
        val activeCoordinator = coordinator ?: return
        coordinator = null
        val completedScopeUnits = scopeUnits
        scopeUnits = 0
        reportStats(activeCoordinator.stats(), completedScopeUnits)
    }

    fun getSummaryStorageSubscriber(
        source: MethodEntryPoint,
        manager: AnalysisUnitRunnerManager,
    ): SummaryEdgeStorageWithSubscribers.Subscriber? {
        if (coordinator == null) return null

        return object : SummaryEdgeStorageWithSubscribers.Subscriber {
            override fun newSummaryEdges(edges: List<Edge>) {
                val deliveries = coordinator?.acceptSummaryEdges(source, edges).orEmpty()
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
        }
    }

    fun onMethodEntryPointActivated(
        methodEntryPoint: MethodEntryPoint,
        manager: AnalysisUnitRunnerManager,
    ) {
        val deliveries = coordinator?.activate(methodEntryPoint).orEmpty()
        submitDeliveries(deliveries, manager)
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

    private fun reportStats(stats: PrescanSeedCoordinator.Stats, scopeUnits: Int) {
        logger.info {
            "Prescan propagation: scopeMethods=${stats.scopeMethods}, scopeUnits=$scopeUnits, " +
                "activeEntryPoints=${stats.activeEntryPoints}, globalSeeds=${stats.globalSeeds}, " +
                "constructorSeeds=${stats.constructorSeeds}, globalDeliveries=${stats.globalDeliveries}, " +
                "constructorDeliveries=${stats.constructorDeliveries}, duplicates=${stats.duplicates}, " +
                "replayedEntryPoints=${stats.replayedEntryPoints}, " +
                "largestGlobalSeedFanOut=${stats.largestGlobalSeedFanOut}, " +
                "largestOwner=${stats.largestOwner?.id ?: "none"}, " +
                "largestOwnerSeedFanOut=${stats.largestOwnerSeedFanOut}"
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

    private data class Seed(
        val sourceMethod: CommonMethod,
        val fact: FinalFactAp,
    )

    private data class DeliveryKey(
        val sourceMethod: CommonMethod,
        val methodEntryPoint: MethodEntryPoint,
    )

    private val scopeMethods = scopeMethods.toHashSet()
    private val activeTargets = linkedMapOf<MethodEntryPoint, ActiveTarget>()

    private val globalSeeds = arrayListOf<Seed>()
    private val globalSeedSet = hashSetOf<FinalFactAp>()
    private val globalVersions = hashMapOf<MethodEntryPoint, Int>()

    private val ownerSeeds = hashMapOf<PrescanInitializerOwner, MutableList<Seed>>()
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

        val deliveries = linkedMapOf<DeliveryKey, MutableList<FinalFactAp>>()

        val globalStart = globalVersions[methodEntryPoint] ?: 0
        if (globalStart < globalSeeds.size) {
            globalSeeds.subList(globalStart, globalSeeds.size).forEach { seed ->
                addDelivery(seed, methodEntryPoint, deliveries)
            }
            globalDeliveries += globalSeeds.size - globalStart
        }
        globalVersions[methodEntryPoint] = globalSeeds.size

        val receiverOwner = target.receiverOwner
        if (receiverOwner != null) {
            val seeds = ownerSeeds[receiverOwner].orEmpty()
            val ownerStart = ownerVersions[methodEntryPoint] ?: 0
            if (ownerStart < seeds.size) {
                seeds.subList(ownerStart, seeds.size).forEach { seed ->
                    addDelivery(seed, methodEntryPoint, deliveries)
                }
                constructorDeliveries += seeds.size - ownerStart
            }
            ownerVersions[methodEntryPoint] = seeds.size
        }

        if (deliveries.isEmpty()) return emptyList()
        replayedEntryPoints++
        return deliveries.toDeliveries()
    }

    @Synchronized
    fun acceptSummaryEdges(
        source: MethodEntryPoint,
        edges: List<Edge>,
    ): List<Delivery> {
        if (edges.isEmpty()) return emptyList()

        val deliveries = linkedMapOf<DeliveryKey, MutableList<FinalFactAp>>()
        for (edge in edges) {
            if (edge !is Edge.ZeroToFact) continue

            val seed = Seed(source.method, edge.factAp)
            when (edge.factAp.base) {
                AccessPathBase.ClassStatic -> addGlobalSeed(seed, deliveries)
                AccessPathBase.This -> {
                    if (source.method !in scopeMethods) continue
                    val owner = policy.initializerOwner(source.method) ?: continue
                    addOwnerSeed(owner, seed, deliveries)
                }
                else -> Unit
            }
        }

        return deliveries.toDeliveries()
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
        seed: Seed,
        deliveries: MutableMap<DeliveryKey, MutableList<FinalFactAp>>,
    ) {
        if (!globalSeedSet.add(seed.fact)) {
            duplicates++
            return
        }

        globalSeeds += seed
        val version = globalSeeds.size
        for (methodEntryPoint in activeTargets.keys) {
            addDelivery(seed, methodEntryPoint, deliveries)
            globalVersions[methodEntryPoint] = version
            globalDeliveries++
        }
    }

    private fun addOwnerSeed(
        owner: PrescanInitializerOwner,
        seed: Seed,
        deliveries: MutableMap<DeliveryKey, MutableList<FinalFactAp>>,
    ) {
        val seedSet = ownerSeedSets.getOrPut(owner, ::hashSetOf)
        if (!seedSet.add(seed.fact)) {
            duplicates++
            return
        }

        val seeds = ownerSeeds.getOrPut(owner, ::arrayListOf)
        seeds += seed
        val version = seeds.size
        for ((methodEntryPoint, target) in activeTargets) {
            if (target.receiverOwner != owner) continue
            addDelivery(seed, methodEntryPoint, deliveries)
            ownerVersions[methodEntryPoint] = version
            constructorDeliveries++
        }
    }

    private fun addDelivery(
        seed: Seed,
        methodEntryPoint: MethodEntryPoint,
        deliveries: MutableMap<DeliveryKey, MutableList<FinalFactAp>>,
    ) {
        val key = DeliveryKey(seed.sourceMethod, methodEntryPoint)
        deliveries.getOrPut(key, ::arrayListOf) += seed.fact
    }

    private fun Map<DeliveryKey, List<FinalFactAp>>.toDeliveries(): List<Delivery> =
        map { (key, facts) -> Delivery(key.sourceMethod, key.methodEntryPoint, facts) }
}
