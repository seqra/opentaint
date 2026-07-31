package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.F2FBBuilder
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.collections.plusAssign
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

class MethodInitialToFinalApSummaries(
    methodInitialStatement: CommonInst,
    override val apManager: TreeApManager,
) : CommonF2FSummary<AccessPath.AccessNode?, AccessTreeNode>(methodInitialStatement),
    TreeInitialApAccess, TreeFinalApAccess {
    override fun createStorage(): Storage<AccessPath.AccessNode?, AccessTreeNode> =
        MethodTaintedSummariesGroupedByFactStorage(apManager)
}

private interface ModifiableStorage {
    fun getAndResetDelta(): Sequence<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>
    fun summaries(): F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>?
}

private abstract class F2FInitialStorage<SN : F2FInitialStorage<SN, S>, S : ModifiableStorage>(
    apManager: TreeApManager,
) : AccessBasedStorage<SN>(apManager) {
    var current: S? = null

    fun filterSummariesTo(dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>, containsPattern: AccessTreeNode) {
        filterContains(containsPattern).forEach { node ->
            node.current?.summaries()?.let { dst.add(it) }
        }
    }

    override fun collectNodesContainsAccessor(
        pattern: AccessTreeNode,
        accessor: AccessorIdx,
        nodes: MutableList<SN>
    ) {
        if (accessor == ANY_ACCESSOR_IDX) {
            nodes += allNodes()
            return
        }

        super.collectNodesContainsAccessor(pattern, accessor, nodes)
    }

    fun collectAllSummariesTo(dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>) {
        allNodes().forEach { node ->
            node.current?.summaries()?.let { dst.add(it) }
        }
    }

    override fun printStorageNode(): String = current.toString()
}

private class MethodTaintedSummariesInitialApStorage(
    apManager: TreeApManager,
) : F2FInitialStorage<MethodTaintedSummariesInitialApStorage, MethodTaintedSummariesMergingStorage>(apManager) {
    override fun createStorage() = MethodTaintedSummariesInitialApStorage(manager)

    fun getOrCreate(initialAccess: AccessPath.AccessNode?): MethodTaintedSummariesMergingStorage =
        getOrCreateNode(initialAccess).getOrCreateCurrent(initialAccess)

    private fun getOrCreateCurrent(access: AccessPath.AccessNode?) =
        current ?: MethodTaintedSummariesMergingStorage(manager, access).also { current = it }
}

private open class MethodTaintedSummariesIdStorage(
    apManager: TreeApManager,
) : F2FInitialStorage<MethodTaintedSummariesIdStorage, SummariesIdStorageNode>(apManager) {

    override fun createStorage() = MethodTaintedSummariesIdStorage(manager)

    fun add(initialAccess: AccessPath.AccessNode?, exclusion: ExclusionSet): SummariesIdStorageNode? {
        val storageNode = try {
            getOrCreateNode(initialAccess)
        } catch (_: NodeSubsumedException) {
            return null
        }

        val node = storageNode.getOrCreateCurrent(initialAccess)
        if (!node.add(exclusion)) return null

        val nodeExclusion = node.exclusion ?: return node
        storageNode.removeChildren { accessor, _ ->
            val accessorInstance = with(manager) { accessor.accessor }
            !nodeExclusion.contains(accessorInstance)
        }

        return node
    }

    override fun getOrCreateChild(accessor: AccessorIdx): MethodTaintedSummariesIdStorage {
        val curExclusion = current?.exclusion ?: return super.getOrCreateChild(accessor)

        val accessorInstance = with(manager) { accessor.accessor }
        if (!curExclusion.contains(accessorInstance)) {
            throw NodeSubsumedException()
        }

        return super.getOrCreateChild(accessor)
    }

    override fun findChild(accessor: AccessorIdx): MethodTaintedSummariesIdStorage? {
        val curExclusion = current?.exclusion ?: return super.findChild(accessor)

        val accessorInstance = with(manager) { accessor.accessor }
        if (!curExclusion.contains(accessorInstance)) {
            return null
        }

        return super.findChild(accessor)
    }

    private fun getOrCreateCurrent(access: AccessPath.AccessNode?) =
        current ?: SummariesIdStorageNode(manager, access).also { current = it }

    private class NodeSubsumedException : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }
}

private class SummariesIdStorageNode(
    val apManager: TreeApManager,
    val initialAccess: AccessPath.AccessNode?
): ModifiableStorage {
    private val finalAccess = with(apManager) {
        if (initialAccess == null) {
            abstractNode
        } else {
            createAbstractNodeFromAccessors(initialAccess.toList())
        }
    }

    var exclusion: ExclusionSet? = null
    private var delta: ExclusionSet? = null

    fun add(addedEx: ExclusionSet): Boolean {
        val currentExclusion = exclusion
        if (currentExclusion == null) {
            exclusion = addedEx
            delta = addedEx
            return true
        }

        val mergedExclusion = currentExclusion.intersect(addedEx)
        if (mergedExclusion === currentExclusion) {
            return false
        }

        exclusion = mergedExclusion
        delta = mergedExclusion
        return true
    }

    override fun getAndResetDelta(): Sequence<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>> {
        val d = delta?.also { delta = null } ?: return emptySequence()
        return FactToFactEdgeBuilderBuilder(apManager)
            .setInitialAp(initialAccess)
            .setExitAp(finalAccess)
            .setExclusion(d)
            .let { sequenceOf(it) }
    }

    override fun summaries(): F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>? {
        val exclusion = this.exclusion ?: return null
        return FactToFactEdgeBuilderBuilder(apManager)
            .setInitialAp(initialAccess)
            .setExitAp(finalAccess)
            .setExclusion(exclusion)
    }
}

private class MethodTaintedSummariesGroupedByFactStorage(
    apManager: TreeApManager,
) : CommonF2FSummary.Storage<AccessPath.AccessNode?, AccessTreeNode> {
    private val idEdges = MethodTaintedSummariesIdStorage(apManager)
    private val nonUniverseAccessPath = MethodTaintedSummariesInitialApStorage(apManager)

    override fun add(
        edges: List<CommonF2FSummary.StorageEdge<AccessPath.AccessNode?, AccessTreeNode>>,
        added: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>
    ) {
        addNonUniverseEdges(edges, added)
    }

    private fun addNonUniverseEdges(
        edges: List<CommonF2FSummary.StorageEdge<AccessPath.AccessNode?, AccessTreeNode>>,
        added: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>
    ) {
        val modifiedStorages = mutableListOf<ModifiableStorage>()

        for (edge in edges) {
            addNonUniverseEdge(edge.initial, edge.final, edge.exclusion, modifiedStorages)
        }

        modifiedStorages.flatMapTo(added) { it.getAndResetDelta() }
    }

    private fun addNonUniverseEdge(
        initialAccess: AccessPath.AccessNode?,
        exitAccess: AccessTreeNode,
        exclusion: ExclusionSet,
        modifiedStorages: MutableList<ModifiableStorage>
    ) {
        val matchResult = exitAccess.splitOnMatching(initialAccess)
        val nonMatchedExitAccess = when (matchResult) {
            is AccessTreeNode.MatchResult.MatchedWithRemainder -> {
                val storage = idEdges.add(initialAccess, exclusion)
                if (storage != null) {
                    modifiedStorages.add(storage)
                }

                matchResult.remainder
            }

            is AccessTreeNode.MatchResult.NotMatched -> exitAccess
        }

        if (nonMatchedExitAccess != null) {
            val storage = nonUniverseAccessPath.getOrCreate(initialAccess)
            val storageModified = storage.add(nonMatchedExitAccess, exclusion)

            if (storageModified) {
                modifiedStorages.add(storage)
            }
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>,
        initialFactPatter: AccessTreeNode?
    ) {
        if (initialFactPatter != null) {
            filterSummariesTo(dst, initialFactPatter)
        } else {
            collectAllSummariesTo(dst)
        }
    }

    private fun filterSummariesTo(dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>, containsPattern: AccessTreeNode) {
        idEdges.filterSummariesTo(dst, containsPattern)
        nonUniverseAccessPath.filterSummariesTo(dst, containsPattern)
    }

    private fun collectAllSummariesTo(dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>) {
        idEdges.collectAllSummariesTo(dst)
        nonUniverseAccessPath.collectAllSummariesTo(dst)
    }
}

private class MethodTaintedSummariesMergingStorage(
    val apManager: TreeApManager,
    val initialAccess: AccessPath.AccessNode?
) : ModifiableStorage {
    private var exclusion: ExclusionSet? = null
    private val treeStorage = MergingTreeSummaryStorage(apManager)

    fun add(exitAccess: AccessTreeNode, addedEx: ExclusionSet): Boolean {
        val currentExclusion = exclusion
        if (currentExclusion == null) {
            exclusion = addedEx
            treeStorage.add(exitAccess)
            return true
        }

        val mergedExclusion = currentExclusion.union(addedEx)
        if (mergedExclusion === currentExclusion) {
            return treeStorage.add(exitAccess)
        }

        treeStorage.add(exitAccess)
        exclusion = mergedExclusion

        return true
    }

    override fun getAndResetDelta(): Sequence<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>> {
        val delta = treeStorage.getAndResetDelta() ?: return emptySequence()

        return FactToFactEdgeBuilderBuilder(apManager)
            .setInitialAp(initialAccess)
            .setExitAp(delta)
            .setExclusion(exclusion!!)
            .let { sequenceOf(it) }
    }

    override fun summaries(): F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>? {
        val exclusion = this.exclusion ?: return null
        val edges = this.treeStorage.edges() ?: return null
        return FactToFactEdgeBuilderBuilder(apManager)
            .setInitialAp(initialAccess)
            .setExitAp(edges)
            .setExclusion(exclusion)
    }
}

private class FactToFactEdgeBuilderBuilder(
    override val apManager: TreeApManager,
) : F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>(),
    TreeInitialApAccess, TreeFinalApAccess {
    override fun nonNullIAP(iap: AccessPath.AccessNode?): AccessPath.AccessNode? = iap
}
