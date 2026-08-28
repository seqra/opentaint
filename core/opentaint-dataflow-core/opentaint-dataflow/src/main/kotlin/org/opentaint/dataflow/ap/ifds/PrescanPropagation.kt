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

    fun onNewSummaryStorage(
        storage: SummaryEdgeStorageWithSubscribers,
        manager: AnalysisUnitRunnerManager,
    ) {
        val activeCoordinator = coordinator ?: return
        val source = storage.methodEntryPoint

        storage.subscribeOnEdges(object : SummaryEdgeStorageWithSubscribers.Subscriber {
            override fun newSummaryEdges(edges: List<Edge>) {
                if (coordinator !== activeCoordinator) return
                val deliveries = activeCoordinator.acceptSummaryEdges(source, edges)
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

    private fun reportStats(stats: PrescanSeedCoordinator.Stats, scopeUnits: Int) {
        logger.info {
            "Prescan propagation: scopeMethods=${stats.scopeMethods}, scopeUnits=$scopeUnits, " +
                "targetEntryPoints=${stats.targetEntryPoints}, globalSeeds=${stats.globalSeeds}, " +
                "constructorSeeds=${stats.constructorSeeds}, globalDeliveries=${stats.globalDeliveries}, " +
                "constructorDeliveries=${stats.constructorDeliveries}, duplicates=${stats.duplicates}, " +
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
