package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet.Empty
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactSideEffectSummariesApStorage
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactList
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodAccessPathSubscription
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesNDInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodNDInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import org.opentaint.dataflow.ap.ifds.access.util.contentKey
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.cfg.CommonInst

class TreeApManager(
    override val anyAccessorUnrollStrategy: AnyAccessorUnrollStrategy,
    refManager: RefManager,
    override val cancellation: Cancellation,
    preInternAccessors: Iterable<Accessor> = emptyList(),
) : ApManager {
    val refManager = refManager.softRefManager("Tree")

    val interner = AccessorInterner().apply { preIntern(preInternAccessors) }

    // Content key per accessor index, cached: key MATERIAL for canonical fact keys, not an
    // ordering. Ordering decisions go through [accessorIdxContentOrder] below.
    private val contentOrderKeys = java.util.concurrent.ConcurrentHashMap<Int, String>()

    // Resolution cache for the comparator's hot path: the interner read takes its storage
    // lock, so resolve each index once. Only successful resolutions are cached -- caching
    // a transient failure would freeze a wrong ordering for the accessor's lifetime.
    private val accessorsByIdx = java.util.concurrent.ConcurrentHashMap<Int, Accessor>()

    private fun resolvedAccessor(idx: AccessorIdx): Accessor? =
        accessorsByIdx[idx] ?: interner.accessor(idx)?.also { accessorsByIdx.putIfAbsent(idx, it) }

    /**
     * The canonical walk order for idx-keyed collections: the cached content-key string.
     * Walks whose emission order can reach edge creation sort with this, so the order is a
     * function of the accessor content and never of the arrival order in which indices
     * were assigned across analysis threads. The string order (not Accessor's Comparable)
     * is deliberate -- it is the layout the whole determinism verification base was
     * measured under; see the note on [AccessorInterner.preIntern].
     */
    val accessorIdxContentOrder: Comparator<AccessorIdx> =
        Comparator { a, b -> accessorContentKey(a).compareTo(accessorContentKey(b)) }

    override fun factContentKey(fact: org.opentaint.dataflow.ap.ifds.access.FinalFactAp): String {
        fact as AccessTree
        return buildString {
            append(fact.base)
            append('/')
            nodeContentKey(fact.access, this)
            append('/')
            append(fact.exclusions)
        }
    }

    override fun factContentKey(fact: org.opentaint.dataflow.ap.ifds.access.InitialFactAp): String =
        fact.toString() // AccessPath is a chain, printed in path order: run-stable already

    private fun nodeContentKey(node: AccessTree.AccessNode, sb: StringBuilder) {
        if (node.isAbstract) sb.append('*')
        if (node.isFinal) sb.append('$')
        val entries = ArrayList<Pair<AccessorIdx, AccessTree.AccessNode>>(4)
        node.forEachAccessor { a, child -> entries.add(a to child) }
        entries.sortWith(compareBy(accessorIdxContentOrder) { it.first })
        for ((a, child) in entries) {
            sb.append('(').append(accessorContentKey(a)).append(':')
            nodeContentKey(child, sb)
            sb.append(')')
        }
    }

    fun accessorContentKey(idx: AccessorIdx): String {
        contentOrderKeys[idx]?.let { return it }
        val accessor = resolvedAccessor(idx) ?: return "\u0000$idx"
        return contentOrderKeys.computeIfAbsent(idx) { accessor.contentKey() }
    }

    val Accessor.idx: AccessorIdx
        get() = interner.index(this)

    val AccessorIdx.accessor: Accessor
        get() = interner.accessor(this)
            ?: error("Accessor not found: $this")

    fun isCoveredByAny(accessor: AccessorIdx) =
        anyAccessorUnrollStrategy.unrollAccessor(accessor.accessor)

    override fun initialFactAbstraction(methodInitialStatement: CommonInst): InitialFactAbstraction =
        TreeInitialFactAbstraction(this)

    override fun methodEdgesFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesFinalApSet =
        MethodEdgesFinalTreeApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesInitialToFinalApSet = MethodEdgesInitialToFinalTreeApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesNDInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesNDInitialToFinalApSet =
        MethodEdgesNDInitialToFinalTreeApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun accessPathSubscription(): MethodAccessPathSubscription =
        MethodTreeAccessPathSubscription(this)

    override fun sideEffectRequirementApStorage(): SideEffectRequirementApStorage =
        SideEffectRequirementTreeApStorage(this)

    override fun methodFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodFinalApSummariesStorage =
        MethodFinalTreeApSummariesStorage(methodInitialStatement, this)

    override fun methodInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodInitialToFinalApSummariesStorage =
        MethodInitialToFinalApSummaries(methodInitialStatement, this)

    override fun methodNDInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodNDInitialToFinalApSummariesStorage =
        MethodNDInitialToFinalApSummaries(methodInitialStatement, this)

    override fun factSideEffectSummariesApStorage(methodInitialStatement: CommonInst): FactSideEffectSummariesApStorage =
        FactSideEffectSummariesTreeApStorage(methodInitialStatement, this)

    override fun listEdgeCompressionRequired(edge: Edge): Boolean {
        val fact = when (edge) {
            is Edge.ZeroToZero -> return false
            is Edge.FactToFact -> edge.factAp
            is Edge.NDFactToFact -> edge.factAp
            is Edge.ZeroToFact -> edge.factAp
        }
        return TreeFinalFactList.factCompressionRequired(fact)
    }

    override fun finalFactList(): FinalFactList = TreeFinalFactList(this)

    override fun mostAbstractInitialAp(base: AccessPathBase): InitialFactAp =
        AccessPath(this, base, access = null, exclusions = Empty)

    override fun mostAbstractFinalAp(base: AccessPathBase): FinalFactAp =
        AccessTree(this, base, abstractNode, exclusions = Empty)

    override fun createFinalAp(base: AccessPathBase, exclusions: ExclusionSet): FinalFactAp =
        AccessTree(this,base, finalNode, exclusions)

    override fun createFinalInitialAp(base: AccessPathBase, exclusions: ExclusionSet): InitialFactAp =
        AccessPath(this, base, access = null, exclusions).prependAccessor(FinalAccessor)

    override fun createSerializer(context: SummarySerializationContext): ApSerializer {
        return TreeSerializer(this, context)
    }

    val emptyNode = AccessNode.createInitialNode(
        this,
        isAbstract = false, isFinal = false,
    )

    val abstractNode = AccessNode.createInitialNode(
        this,
        isAbstract = true, isFinal = false,
    )

    val finalNode = AccessNode.createInitialNode(
        this,
        isAbstract = false, isFinal = true,
    )

    val abstractFinalNode = AccessNode.createInitialNode(
        this,
        isAbstract = true, isFinal = true,
    )
}
