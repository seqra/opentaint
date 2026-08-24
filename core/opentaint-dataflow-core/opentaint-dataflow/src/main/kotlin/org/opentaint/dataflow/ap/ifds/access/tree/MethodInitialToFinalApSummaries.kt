package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.F2FBBuilder
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

class MethodInitialToFinalApSummaries(
    methodInitialStatement: CommonInst,
    override val apManager: TreeApManager,
) : CommonF2FSummary<AccessPath.AccessNode?, AccessTreeNode>(methodInitialStatement),
    TreeInitialApAccess, TreeFinalApAccess {

    private val premiseCounter: MethodSummaryPremises? =
        if (SummaryPremiseDiagnostics.enabled) {
            SummaryPremiseDiagnostics.counterFor(methodInitialStatement.location.method.toString())
        } else {
            null
        }

    override fun createStorage(): Storage<AccessPath.AccessNode?, AccessTreeNode> =
        MethodTaintedSummariesGroupedByFactStorage(apManager, premiseCounter)
}

private interface ModifiableStorage {
    fun getAndResetDelta(): Sequence<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>
    fun summaries(): F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>?
}

private abstract class F2FInitialStorage<SN : F2FInitialStorage<SN, S>, S : ModifiableStorage>(
    apManager: TreeApManager,
    /** Diagnostics only; propagated through [createStorage] so every trie node reports to one method. */
    @JvmField val premiseCounter: MethodSummaryPremises?,
) : AccessBasedStorage<SN>(apManager) {
    var current: S? = null

    fun filterSummariesTo(dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>, containsPattern: AccessTreeNode) {
        filterContains(containsPattern).forEach { node ->
            node.current?.summaries()?.let { dst.add(it) }
        }
    }

    /*
     * There used to be a `collectNodesContainsAccessor` override here: a caller fact carrying
     * `[any]` activated the ENTIRE premise subtree (`nodes += allNodes()`), pattern discarded.
     * That blanket was not a rule, it was compensation -- a premise could never hold `[any]`, so
     * `children.get(ANY_ACCESSOR_IDX)` was always null, and without it a whole-subtree-tainted
     * caller fact activated no deeper premise at all.
     *
     * Premises can hold `[any]` now, so the compensation became a real rule and moved to
     * `AccessBasedStorage.collectNodesContainsAnyAccessor`, where the two side-effect storages get
     * it too (design 6.5 and 6.7). The result is a subset of `allNodes()`: every node it drops is
     * reachable only through an accessor `[any]` provably cannot step over.
     */

    fun collectAllSummariesTo(dst: MutableList<F2FBBuilder<AccessPath.AccessNode?, AccessTreeNode>>) {
        allNodes().forEach { node ->
            node.current?.summaries()?.let { dst.add(it) }
        }
    }

    override fun printStorageNode(): String = current.toString()
}

private class MethodTaintedSummariesInitialApStorage(
    apManager: TreeApManager,
    premiseCounter: MethodSummaryPremises?,
) : F2FInitialStorage<MethodTaintedSummariesInitialApStorage, MethodTaintedSummariesMergingStorage>(apManager, premiseCounter) {
    override fun createStorage() = MethodTaintedSummariesInitialApStorage(manager, premiseCounter)

    fun getOrCreate(initialAccess: AccessPath.AccessNode?): MethodTaintedSummariesMergingStorage =
        getOrCreateNode(initialAccess).getOrCreateCurrent(initialAccess)

    private fun getOrCreateCurrent(access: AccessPath.AccessNode?) =
        current ?: MethodTaintedSummariesMergingStorage(manager, access)
            .also {
                current = it
                premiseCounter?.record(access, identity = false)
            }
}

private open class MethodTaintedSummariesIdStorage(
    apManager: TreeApManager,
    premiseCounter: MethodSummaryPremises?,
) : F2FInitialStorage<MethodTaintedSummariesIdStorage, SummariesIdStorageNode>(apManager, premiseCounter) {

    override fun createStorage() = MethodTaintedSummariesIdStorage(manager, premiseCounter)

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

    /**
     * Descending below an id edge is allowed only for accessors the edge EXCLUDES; anything else is
     * already covered by it, so the deeper premise is dropped (via [NodeSubsumedException], caught
     * silently in [add]).
     *
     * `[any]` is always dropped here, and that is CORRECT -- do not "fix" it (design 6.4). An
     * exclusion set is only ever populated from a concrete accessor read off a memory access
     * (`JIRMethodSequentFlowFunction.propagateAbstractFactWithFieldExcluded`,
     * `GoMethodSequentFlowFunction.F2FPropagationContext.propagateFactWithAccessorExclude`) or from
     * `TypeInfoGroupAccessor` (`CallTypeInfoUtil`), never from `AnyAccessor`, so
     * `contains(AnyAccessor)` is false and an `[any]` link never gets past this check.
     *
     * Nothing is lost, because an id edge at `p` is an identity summary and `p.[any].*` denotes a
     * subset of `p.*`. The apparent counter-example -- an id edge excluding `f`, against a premise
     * `p.[any]` whose `[any]` covers `f` -- does not bite either: `AccessTree.delta` filters the
     * residual with `AccessNode.filter(exclusion)`, which drops a child only when its own accessor
     * is in the set. `AnyAccessor` never is, so an `[any]`-headed residual survives the filter
     * intact, the id edge fires for the `[any]`-carrying caller fact, and the identity summary
     * passes it through. That the pass-through also carries the `f` part the exclusion meant to
     * remove is an over-approximation -- a false positive at worst, never a lost flow -- and it is
     * pre-existing, independent of `[any]` being representable in a premise.
     */
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
        current ?: SummariesIdStorageNode(manager, access).also {
            current = it
            premiseCounter?.record(access, identity = true)
        }

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
    premiseCounter: MethodSummaryPremises?,
) : CommonF2FSummary.Storage<AccessPath.AccessNode?, AccessTreeNode> {
    private val idEdges = MethodTaintedSummariesIdStorage(apManager, premiseCounter)
    private val nonUniverseAccessPath = MethodTaintedSummariesInitialApStorage(apManager, premiseCounter)

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
