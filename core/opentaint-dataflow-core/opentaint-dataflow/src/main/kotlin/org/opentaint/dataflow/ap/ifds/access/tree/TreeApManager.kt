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
import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion
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
) : ApManager {
    val refManager = refManager.softRefManager("Tree")

    val interner = AccessorInterner()

    // Content key per accessor index, cached for canonical fact keys and hashes.
    private val contentOrderKeys = java.util.concurrent.ConcurrentHashMap<Int, String>()

    // Resolution cache for the comparator's hot path: the interner read takes its storage
    // lock, so resolve each index once. Only successful resolutions are cached -- caching
    // a transient failure would freeze a wrong ordering for the accessor's lifetime.
    private val accessorsByIdx = java.util.concurrent.ConcurrentHashMap<Int, Accessor>()

    private fun resolvedAccessor(idx: AccessorIdx): Accessor? =
        accessorsByIdx[idx] ?: interner.accessor(idx)?.also { accessorsByIdx.putIfAbsent(idx, it) }

    /**
     * The canonical walk order for idx-keyed collections: [Accessor]'s natural order.
     * Walks whose emission order can reach edge creation sort with this, so the order is a
     * function of the accessor content and never of the arrival order in which indices
     * were assigned across analysis threads.
     */
    val accessorIdxContentOrder: Comparator<AccessorIdx> =
        Comparator { a, b ->
            val left = resolvedAccessor(a) ?: error("Accessor not found: $a")
            val right = resolvedAccessor(b) ?: error("Accessor not found: $b")
            left.compareTo(right)
        }

    override fun factContentKey(fact: org.opentaint.dataflow.ap.ifds.access.FinalFactAp): String {
        fact as AccessTree
        return buildString {
            append(fact.base)
            append('/')
            nodeContentKey(fact.access, this)
            append('/')
            append(exclusionContentKey(fact.exclusions))
        }
    }

    override fun factContentKey(fact: org.opentaint.dataflow.ap.ifds.access.InitialFactAp): String {
        fact as AccessPath
        return buildString {
            append(fact.base)
            var node = fact.access
            while (node != null) {
                appendFramed(accessorContentKey(node.accessor), this)
                node = node.next
            }
            append("/*/").append(exclusionContentKey(fact.exclusions))
        }
    }

    private fun nodeContentKey(node: AccessTree.AccessNode, sb: StringBuilder) {
        if (node.isAbstract) sb.append('*')
        if (node.isFinal) sb.append('$')
        node.deepAccessorExclusion?.let { sb.append(deepExclusionContentKey(it)) }
        val entries = ArrayList<Pair<AccessorIdx, AccessTree.AccessNode>>(4)
        node.forEachAccessor { a, child -> entries.add(a to child) }
        entries.sortWith(compareBy(accessorIdxContentOrder) { it.first })
        for ((a, child) in entries) {
            sb.append('(')
            appendFramed(accessorContentKey(a), sb)
            nodeContentKey(child, sb)
            sb.append(')')
        }
    }

    fun accessorContentKey(idx: AccessorIdx): String {
        contentOrderKeys[idx]?.let { return it }
        val accessor = resolvedAccessor(idx) ?: error("Accessor not found: $idx")
        return contentOrderKeys.computeIfAbsent(idx) { accessor.contentKey() }
    }

    fun accessorContentHash(idx: AccessorIdx): Int = accessorContentKey(idx).hashCode()

    private fun exclusionContentKey(exclusion: ExclusionSet): String = when (exclusion) {
        ExclusionSet.Empty -> "{}"
        ExclusionSet.Universe -> "*"
        is ExclusionSet.Concrete -> exclusion.set.asSequence()
            .map { it.contentKey() }
            .sorted()
            .joinToString(prefix = "{", postfix = "}") { "${it.length}:$it" }
    }

    fun deepExclusionContentKey(exclusion: DeepAccessorExclusion): String = buildString {
        fun appendAccessors(accessors: IntArray) {
            accessors.asSequence().map(::accessorContentKey).sorted()
                .forEach { appendFramed(it, this@buildString) }
        }
        append("!{d0=")
        appendAccessors(exclusion.accessorsFromDepth0)
        append(";d1=")
        appendAccessors(exclusion.accessorsFromDepth1)
        append('}')
    }

    private fun appendFramed(value: String, sb: StringBuilder) {
        sb.append(value.length).append(':').append(value)
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
