package org.opentaint.dataflow.ap.ifds.access.cactus

import kotlinx.collections.immutable.persistentHashMapOf
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.F2FBBuilder
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.dataflow.ap.ifds.access.cactus.AccessCactus.AccessNode as AccessCactusNode

class MethodInitialToFinalApSummaries(
    methodInitialStatement: CommonInst,
) : CommonF2FSummary<AccessPathWithCycles.AccessNode?, AccessCactusNode>(methodInitialStatement),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createStorage(): Storage<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode> =
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

    fun collectAllSummaries(dst: MutableList<F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>>) {
        initialAccessToStorage.values.forEach { storage ->
            storage.summaries()?.let { dst.add(it) }
        }
    }
}

private class MethodTaintedSummariesGroupedByFactStorage
    : CommonF2FSummary.Storage<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode> {
    private val nonUniverseAccessPath = MethodTaintedSummariesInitialApStorage()

    override fun add(
        edges: List<CommonF2FSummary.StorageEdge<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>>,
        added: MutableList<F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>>
    ) {
        addNonUniverseEdges(edges, added)
    }

    private fun addNonUniverseEdges(
        edges: List<CommonF2FSummary.StorageEdge<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>>,
        added: MutableList<F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>>
    ) {
        val modifiedStorages = mutableListOf<MethodTaintedSummariesMergingStorage>()

        for (edge in edges) {
            addNonUniverseEdge(edge.initial, edge.final, edge.flowState, modifiedStorages)
        }

        modifiedStorages.flatMapTo(added) { it.getAndResetDelta() }
    }

    private fun addNonUniverseEdge(
        initialAccess: AccessPathWithCycles.AccessNode?,
        exitAccess: AccessCactusNode,
        flowState: FactFlowState,
        modifiedStorages: MutableList<MethodTaintedSummariesMergingStorage>
    ) {
        val storage = nonUniverseAccessPath.getOrCreate(initialAccess)
        val storageModified = storage.add(exitAccess, flowState)

        if (storageModified) {
            modifiedStorages.add(storage)
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>>,
        initialFactPatter: AccessCactus.AccessNode?
    ) {
        nonUniverseAccessPath.collectAllSummaries(dst)
    }
}

private class MethodTaintedSummariesMergingStorage(val initialAccess: AccessPathWithCycles.AccessNode?) {
    private var flowState: FactFlowState? = null
    private var edges: AccessCactusNode? = null
    private var edgesDelta: AccessCactusNode? = null

    fun add(exitAccess: AccessCactusNode, addedState: FactFlowState): Boolean {
        val currentState = flowState
        if (currentState == null) {
            flowState = addedState
            edges = exitAccess
            edgesDelta = exitAccess
            return true
        }

        val currentEdges = edges!!
        val mergedState = currentState join addedState
        if (mergedState === currentState) {
            val (modifiedEdges, modificationDelta) = currentEdges.mergeAddDelta(exitAccess)
            if (modificationDelta == null) return false

            edges = modifiedEdges
            edgesDelta = edgesDelta?.mergeAdd(modificationDelta) ?: modificationDelta
            return true
        }

        val mergedAp = currentEdges.mergeAdd(exitAccess)
        flowState = mergedState
        edges = mergedAp
        edgesDelta = mergedAp

        return true
    }

    fun getAndResetDelta(): Sequence<F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>> {
        val delta = edgesDelta ?: return emptySequence()
        edgesDelta = null

        return FactToFactEdgeBuilderBuilder()
            .setInitialAp(initialAccess)
            .setExitAp(delta)
            .setFlowState(flowState!!)
            .let { sequenceOf(it) }
    }

    fun summaries(): F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>? {
        val flowState = this.flowState ?: return null
        val edges = this.edges!!
        return FactToFactEdgeBuilderBuilder()
            .setInitialAp(initialAccess)
            .setExitAp(edges)
            .setFlowState(flowState)
    }
}

private class FactToFactEdgeBuilderBuilder :
    F2FBBuilder<AccessPathWithCycles.AccessNode?, AccessCactusNode>(),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun nonNullIAP(iap: AccessPathWithCycles.AccessNode?): AccessPathWithCycles.AccessNode? = iap
}
