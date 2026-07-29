package org.opentaint.dataflow.ap.ifds.access.cactus

import kotlinx.collections.immutable.persistentHashMapOf
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.F2FBBuilder
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodInitialToFinalApSummaries(
    methodInitialStatement: CommonInst,
) : CommonF2FSummary<CactusInitialAccess, CactusFinalAccess>(methodInitialStatement),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createStorage(): Storage<CactusInitialAccess, CactusFinalAccess> =
        MethodTaintedSummariesGroupedByFactStorage()
}

private class MethodTaintedSummariesInitialApStorage {
    private var initialAccessToStorage =
        persistentHashMapOf<AccessPathWithCycles.AccessNode?, MethodTaintedSummariesMergingStorage>()

    fun getOrCreate(initialAccess: AccessPathWithCycles.AccessNode?): MethodTaintedSummariesMergingStorage =
        initialAccessToStorage.getOrElse(initialAccess) {
            MethodTaintedSummariesMergingStorage(initialAccess).also {
                initialAccessToStorage = initialAccessToStorage.put(initialAccess, it)
            }
        }

    fun collectAllSummaries(dst: MutableList<F2FBBuilder<CactusInitialAccess, CactusFinalAccess>>) {
        initialAccessToStorage.values.forEach { storage ->
            storage.summaries()?.let { dst.add(it) }
        }
    }
}

private class MethodTaintedSummariesGroupedByFactStorage
    : CommonF2FSummary.Storage<CactusInitialAccess, CactusFinalAccess> {
    private val nonUniverseAccessPath = MethodTaintedSummariesInitialApStorage()

    override fun add(
        edges: List<CommonF2FSummary.StorageEdge<CactusInitialAccess, CactusFinalAccess>>,
        added: MutableList<F2FBBuilder<CactusInitialAccess, CactusFinalAccess>>
    ) {
        addNonUniverseEdges(edges, added)
    }

    private fun addNonUniverseEdges(
        edges: List<CommonF2FSummary.StorageEdge<CactusInitialAccess, CactusFinalAccess>>,
        added: MutableList<F2FBBuilder<CactusInitialAccess, CactusFinalAccess>>
    ) {
        val modifiedStorages = mutableListOf<MethodTaintedSummariesMergingStorage>()

        for (edge in edges) {
            addNonUniverseEdge(
                edge.initial,
                edge.final,
                edge.exclusion,
                modifiedStorages,
            )
        }

        modifiedStorages.flatMapTo(added) { it.getAndResetDelta() }
    }

    private fun addNonUniverseEdge(
        initialAccess: AccessPathWithCycles.AccessNode?,
        exitAccess: CactusFinalAccess,
        exclusion: ExclusionSet,
        modifiedStorages: MutableList<MethodTaintedSummariesMergingStorage>
    ) {
        val storage = nonUniverseAccessPath.getOrCreate(initialAccess)
        val storageModified = storage.add(exitAccess, exclusion)

        if (storageModified) {
            modifiedStorages.add(storage)
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<F2FBBuilder<CactusInitialAccess, CactusFinalAccess>>,
        initialFactPatter: CactusFinalAccess?
    ) {
        nonUniverseAccessPath.collectAllSummaries(dst)
    }
}

private class MethodTaintedSummariesMergingStorage(val initialAccess: AccessPathWithCycles.AccessNode?) {
    private var exclusion: ExclusionSet? = null
    private var edges: CactusFinalAccess? = null
    private var edgesDelta: CactusFinalAccess? = null

    fun add(exitAccess: CactusFinalAccess, addedState: ExclusionSet): Boolean {
        val currentState = exclusion
        if (currentState == null) {
            exclusion = addedState
            edges = exitAccess
            edgesDelta = exitAccess
            return true
        }

        val currentEdges = edges!!
        val mergedState = currentState.union(addedState)
        if (mergedState === currentState) {
            val (modifiedEdges, modificationDelta) = currentEdges.mergeAddDelta(exitAccess)
            if (modificationDelta == null) return false

            edges = modifiedEdges
            edgesDelta = edgesDelta?.mergeAdd(modificationDelta) ?: modificationDelta
            return true
        }

        val mergedAp = currentEdges.mergeAdd(exitAccess)
        exclusion = mergedState
        edges = mergedAp
        edgesDelta = mergedAp

        return true
    }

    fun getAndResetDelta(): Sequence<F2FBBuilder<CactusInitialAccess, CactusFinalAccess>> {
        val delta = edgesDelta ?: return emptySequence()
        edgesDelta = null

        return FactToFactEdgeBuilderBuilder()
            .setInitialAp(initialAccess)
            .setExitAp(delta)
            .setExclusion(exclusion!!)
            .let { sequenceOf(it) }
    }

    fun summaries(): F2FBBuilder<CactusInitialAccess, CactusFinalAccess>? {
        val exclusion = this.exclusion ?: return null
        val edges = this.edges!!
        return FactToFactEdgeBuilderBuilder()
            .setInitialAp(initialAccess)
            .setExitAp(edges)
            .setExclusion(exclusion)
    }
}

private class FactToFactEdgeBuilderBuilder :
    F2FBBuilder<CactusInitialAccess, CactusFinalAccess>(),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun nonNullIAP(iap: CactusInitialAccess?): CactusInitialAccess =
        iap ?: error("iap not initialized")
}
