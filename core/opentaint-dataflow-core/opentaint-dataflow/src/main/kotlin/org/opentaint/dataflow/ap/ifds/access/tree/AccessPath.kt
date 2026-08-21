package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.ANY_ACCESSOR_DEPTH_CHARGE
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.SUBSEQUENT_ARRAY_ELEMENTS_LIMIT
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor
import org.opentaint.dataflow.util.foldRightInt
import org.opentaint.dataflow.util.reversedForEachInt

class AccessPath(
    private val apManager: TreeApManager,
    override val base: AccessPathBase,
    val access: AccessNode?,
    override val exclusions: ExclusionSet
): InitialFactAp {
    override fun rebase(newBase: AccessPathBase): InitialFactAp =
        AccessPath(apManager, newBase, access, exclusions)

    override fun isAbstract(): Boolean = access == null

    override fun exclude(accessor: Accessor): InitialFactAp =
        AccessPath(apManager, base, access, exclusions.add(accessor))

    override fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp =
        AccessPath(apManager, base, access, exclusions)

    /**
     * Every accessor on the chain, INCLUDING [org.opentaint.dataflow.ap.ifds.AnyAccessor].
     *
     * Deliberately asymmetric with the fact side, whose `AccessTree.AccessNode.collectAccessorsTo`
     * always ignores `[any]` (there is a matching note there). A premise's accessor set answers
     * "which links does this premise have", and an `[any]` link is a link: hiding it would make an
     * `[any]`-only premise indistinguishable from a bare, unrefined one, which is exactly the
     * distinction `MethodSideEffectHandlerWithAnyAccessorRequestHandling.handleFactToFact` needs.
     * Consumers that want only concrete accessors must filter `AnyAccessor` out themselves.
     */
    override fun getAllAccessors(): Set<Accessor> =
        access?.accessorList()?.toSet().orEmpty()

    override fun startsWithAccessor(accessor: Accessor): Boolean = with(apManager) {
        if (access == null) return false
        return access.accessor.accessor == accessor
    }

    override fun getStartAccessors(): Set<Accessor> = with(apManager) {
        access?.let { setOf(it.accessor.accessor) } ?: emptySet()
    }

    override fun readAccessor(accessor: Accessor): AccessPath? = with(apManager) {
        if (access == null) return null
        if (access.accessor.accessor != accessor) return null
        return AccessPath(apManager, base, access.next, exclusions)
    }

    override fun prependAccessor(accessor: Accessor): InitialFactAp {
        val accessorIdx = with(apManager) { accessor.idx }

        if (access == null) {
            return AccessPath(apManager, base, AccessNode(apManager, accessorIdx, next = null), exclusions)
        }

        val node = access.addParent(accessorIdx)
        return AccessPath(apManager, base, node, exclusions)
    }

    override fun clearAccessor(accessor: Accessor): InitialFactAp? = with(apManager) {
        if (access == null) return this@AccessPath
        if (access.accessor.accessor != accessor) return this@AccessPath
        return null
    }

    override fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter {
        val node = access ?: return FactTypeChecker.AlwaysCompatibleFilter
        return typeChecker.accessPathCompatibilityFilter(node.accessorList())
    }

    sealed interface AccessPathDelta : InitialFactAp.Delta {
        data object Empty : AccessPathDelta {
            override val isEmpty: Boolean get() = true
            override fun startsWithAccessor(accessor: Accessor): Boolean = false
            override fun getStartAccessors(): Set<Accessor> = emptySet()
            override fun getAllAccessors(): Set<Accessor> = emptySet()
            override fun readAccessor(accessor: Accessor): InitialFactAp.Delta? = null
            override fun isAbstract(): Boolean = true
        }

        data class Delta(val node: AccessNode) : AccessPathDelta {
            override val isEmpty: Boolean get() = false
            override fun startsWithAccessor(accessor: Accessor): Boolean =
                with(node.manager) { node.accessor.accessor == accessor }

            override fun getStartAccessors(): Set<Accessor> =
                with(node.manager) { setOf(node.accessor.accessor) }

            override fun getAllAccessors(): Set<Accessor> =
                node.accessorList().toSet()

            override fun readAccessor(accessor: Accessor): InitialFactAp.Delta? = with(node.manager) {
                if (node.accessor.accessor == accessor) return node.next?.let { Delta(it) }
                return null
            }

            override fun isAbstract(): Boolean = false
        }

        override fun concat(other: InitialFactAp.Delta): InitialFactAp.Delta {
            other as AccessPathDelta

            return when (this) {
                is Empty -> other
                is Delta -> when (other) {
                    is Empty -> this
                    is Delta -> Delta(node.concat(other.node))
                }
            }
        }
    }

    /**
     * Split this premise against a fact into (matched prefix, remaining delta).
     *
     * Note the `otherNode.isAbstract` escape hatch, which `AccessTree.delta` does not have: it lets
     * this premise be LONGER than the fact, matching the remainder against the fact's `*` and
     * returning it as the delta. That includes matching an `[any]` link of the premise against a
     * plain abstract node of the fact -- premise `a.b.[any]` does match fact `base.a.b.*`.
     *
     * That is kept deliberately:
     * - it is not a false match. `*` denotes every path below the node, a strict superset of the
     *   covered sequences `[any]` denotes, so an abstract fact really does cover the `[any]` premise.
     * - the strong precondition of the `[any]` design is a property of SUMMARY APPLICATION, where
     *   `AccessTree.delta`/`getChild` decide which premise a fact activates. This method is not on
     *   that path: its only caller is trace resolution (`MethodTraceResolver`), which explains an
     *   already-decided finding by attributing it to a summary edge.
     * - trace resolution cannot add or remove a reported finding. A vulnerability that resolves to
     *   no trace is still reported, with `trace = null`
     *   (`TaintAnalysisUnitRunnerManager.resolveVulnerabilityTracesWithCancellation`). Tightening
     *   this would therefore buy no soundness and cost trace coverage.
     */
    override fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, InitialFactAp.Delta>> {
        other as AccessTree

        if (base != other.base) return emptyList()

        var node: AccessNode? = access
        var otherNode: AccessTree.AccessNode = other.access
        val accessorsOnPath = IntArrayList()

        while (true) {
            if (node == null) {
                if (otherNode.isAbstract) {
                    return listOf(this to AccessPathDelta.Empty)
                }
                return emptyList()
            }

            val nextOtherNode = if (node.accessor == FINAL_ACCESSOR_IDX) {
                if (otherNode.isFinal) {
                    return listOf(this to AccessPathDelta.Empty)
                }

                null
            } else {
                otherNode.getChild(node.accessor)
            }

            if (nextOtherNode == null) {
                if (otherNode.isAbstract) {
                    val filteredNode = node.filter(other.exclusions) ?: return emptyList()

                    val matchedAccessNode = accessorsOnPath.foldRightInt(null as AccessNode?) { accessor, prevNode ->
                        AccessNode(apManager, accessor, prevNode)
                    }
                    val matchedFact = AccessPath(apManager, base, matchedAccessNode, exclusions)

                    return listOf(matchedFact to AccessPathDelta.Delta(filteredNode))
                }

                return emptyList()
            }

            accessorsOnPath.add(node.accessor)
            node = node.next
            otherNode = nextOtherNode
        }
    }

    /**
     * Head-only: an exclusion set can only ever remove the FIRST link of a delta.
     *
     * `[any]` asymmetry, left as-is deliberately: exclusion sets are only ever populated from
     * concrete accessors, so `AnyAccessor !in exclusion` always holds and an `[any]`-headed delta
     * survives an exclusion `{f}` intact -- even though `[any]` covers `f`, so the delta really does
     * denote `f`-prefixed paths that the exclusion meant to remove. The effect is that the excluded
     * branch is kept rather than dropped: a false positive at worst, never a false negative. The
     * fact side has the same property (see the `filter` call in `AccessTree.delta`).
     */
    private fun AccessNode.filter(exclusion: ExclusionSet): AccessNode? = when (exclusion) {
        ExclusionSet.Empty -> this
        is ExclusionSet.Concrete -> this.takeIf { with(manager) { it.accessor.accessor !in exclusion } }
        ExclusionSet.Universe -> null
    }

    override fun concat(delta: InitialFactAp.Delta): InitialFactAp {
        delta as AccessPathDelta

        when (delta) {
            AccessPathDelta.Empty -> return this
            is AccessPathDelta.Delta -> {
                val node = access?.concat(delta.node) ?: delta.node
                return AccessPath(apManager, base, node, exclusions)
            }
        }
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as AccessPath
        return this == factAp
    }

    override val size: Int
        get() = access?.size ?: 0

    override val depth: Int get() = access?.depth ?: 0

    override fun toString(): String = "$base${access ?: ""}.*/$exclusions"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as AccessPath

        if (base != other.base) return false
        if (access != other.access) return false
        if (exclusions != other.exclusions) return false

        return true
    }

    override fun hashCode(): Int {
        var result = base.hashCode()
        result = 31 * result + access.hashCode()
        result = 31 * result + exclusions.hashCode()
        return result
    }

    class AccessNode(
        val manager: TreeApManager,
        val accessor: AccessorIdx,
        val next: AccessNode?
    ) {
        private val hash: Int

        /**
         * The literal number of links in the chain, `[any]` counted as 1 like everything else.
         *
         * Kept a plain link count on purpose: it is used for STRUCTURAL comparisons, in particular
         * `AccessTree.AccessNode.filterStartsWith` compares a tree node's `maxDepth` against it to
         * prune premises that cannot fit under the fact. Inflating it would over-prune. For the
         * COST-weighted length use [depth].
         */
        val size: Int

        /**
         * The cost-weighted length of the chain: an `[any]` link is charged
         * [ANY_ACCESSOR_DEPTH_CHARGE], every other link 1.
         *
         * An `[any]` stands for an unbounded sequence of covered steps, so charging it as one step
         * would let exactly the premises that admit the deepest facts slip past
         * `MethodAnalyzer.edgeExceedLimit`, which gates an edge on `initialFactAp.depth`. The number
         * is deliberately the same one the fact side charges on `AccessTree.AccessNode.maxDepth` --
         * the two are compared against one budget. See the note at the constant.
         */
        val depth: Int

        init {
            var hash = accessor
            if (next != null) hash += 17 * next.hash
            this.hash = hash
        }

        init {
            var size = 1
            var depth = if (accessor == ANY_ACCESSOR_IDX) ANY_ACCESSOR_DEPTH_CHARGE else 1
            if (next != null) {
                size += next.size
                depth += next.depth
            }
            this.size = size
            this.depth = depth
        }

        override fun hashCode(): Int = hash

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is AccessNode) return false

            if (hash != other.hash) return false
            if (accessor != other.accessor) return false

            return next == other.next
        }

        fun toList(): IntArrayList {
            val result = IntArrayList()
            var node = this
            while (true) {
                result.add(node.accessor)
                node = node.next ?: break
            }
            return result
        }

        /**
         * Append [other] below this chain by re-prepending this chain's accessors onto it.
         *
         * Every link goes through [addParent], so an `[any]` in the LEFT operand is preserved
         * exactly as far as [addParent] preserves it -- which, since [addParent] stopped dropping
         * `ANY_ACCESSOR_IDX`, is fully. No separate handling is needed here.
         */
        fun concat(other: AccessNode): AccessNode {
            val thisAccessors = this.toList()
            var node = other
            thisAccessors.reversedForEachInt { accessor ->
                node = node.addParent(accessor)
            }
            return node
        }

        fun accessorList(): List<Accessor> = toList().map { with(manager) { it.accessor } }

        override fun toString(): String = accessorList().joinToString("") { it.toSuffix() }

        fun addParent(accessor: AccessorIdx): AccessNode {
            checkNoClassStaticAccessor()

            return when {
                accessor == FINAL_ACCESSOR_IDX -> error("Final parent")
                accessor == ELEMENT_ACCESSOR_IDX -> AccessNode(
                    manager, ELEMENT_ACCESSOR_IDX,
                    limitElementAccess(limit = SUBSEQUENT_ARRAY_ELEMENTS_LIMIT)
                )
                accessor.isFieldAccessor() -> AccessNode(manager, accessor, limitFieldAccess(accessor))
                accessor.isStaticAccessor() -> AccessNode(manager, accessor, this)
                accessor.isTaintMarkAccessor() -> AccessNode(manager, accessor, this)
                accessor == VALUE_ACCESSOR_IDX -> {
                    check(this.accessor.isTaintMarkAccessor()) {
                        "Value accessor can only be prepended before a taint mark"
                    }
                    AccessNode(manager, accessor, this)
                }

                accessor == ANY_ACCESSOR_IDX -> prependAnyAccessor()

                accessor == TYPE_INFO_GROUP_ACCESSOR_IDX -> AccessNode(manager, accessor, this)
                accessor.isTypeInfoAccessor() -> AccessNode(manager, accessor, this)

                else -> error("Unsupported accessor $accessor")
            }
        }

        private fun checkNoClassStaticAccessor() {
            var node: AccessNode? = this
            while (node != null) {
                check(!node.accessor.isStaticAccessor()) {
                    "At most one ClassStaticAccessor is allowed in access path"
                }
                node = node.next
            }
        }

        private fun limitElementAccess(limit: Int): AccessNode? {
            if (accessor != ELEMENT_ACCESSOR_IDX) return this

            if (limit > 0) {
                val limitedChild = next?.limitElementAccess(limit - 1)
                if (limitedChild === next) return this
                return AccessNode(manager, accessor, limitedChild)
            }

            return collapseElementAccess()
        }


        private fun collapseElementAccess(): AccessNode? {
            var node = this
            while (true) {
                if (node.accessor != ELEMENT_ACCESSOR_IDX) return node
                node = node.next ?: return null
            }
        }

        /**
         * Build `[any].this`, maintaining on the chain the same representation invariant the fact
         * side maintains in `AccessTree.AccessNode.prependAnyAccessor`: no `[any]` is reachable
         * from another `[any]` through a covered-only path.
         *
         * Under the zero-or-more reading of `[any]` the collapse is an IDENTITY, not an
         * approximation: for `x`, `y` covered by `[any]`, `[any].x.y.[any].S` and `[any].S` denote
         * the same path set, because `w.x.y.v` ranges over exactly the same covered sequences as a
         * single `w'`.
         *
         * The scan stops at the first accessor `[any]` does not cover -- a taint mark, a static, a
         * type-info accessor, `[value]`, `[final]` -- because the identity does not hold across one.
         * There the `[any]` is simply prepended: `[any]` onto `![m].S` is `[any].![m].S`, never a
         * collapse. (On the fact side an `[any]` below a mark is unconstructible outright; here it
         * is enough that the scan does not cross one.)
         *
         * The predicate is [TreeApManager.isCoveredByAny], never `AnyAccessor.containsAccessor`:
         * coverage is the unroll strategy's decision, and only it agrees with what `getChild` on
         * the fact side will actually match.
         */
        private fun prependAnyAccessor(): AccessNode {
            var node: AccessNode? = this
            while (node != null) {
                val accessor = node.accessor
                if (accessor == ANY_ACCESSOR_IDX) {
                    // the whole covered run plus the inner `[any]` collapses into one `[any]`
                    return AccessNode(manager, ANY_ACCESSOR_IDX, node.next)
                }

                if (!manager.isCoveredByAny(accessor)) break

                node = node.next
            }

            return AccessNode(manager, ANY_ACCESSOR_IDX, this)
        }

        /**
         * The repeated-field cycle collapse: prepending `.y` onto a chain that already contains a
         * `y` truncates the chain to just below that `y`, which is what stops a cyclic data
         * structure from generating an unbounded family of premises.
         *
         * The scan stops at an `[any]` and collapses nothing. An `[any]` between the new `y` and the
         * old one means the two occurrences need not denote the same field of the same object -- an
         * arbitrary covered sequence separates them -- so this is not a cycle. Walking through it
         * would turn `y` prepended onto `x.[any].y.b.$` into `b.$`, discarding the `[any]` and the
         * whole prefix above it and leaving a premise anchored at a different position entirely.
         *
         * The element-run analogues [limitElementAccess] and [collapseElementAccess] need no such
         * guard: both terminate at the first non-element accessor, and `[any]` is not an element
         * accessor, so an `[any]` already breaks an element run instead of being walked through.
         */
        private fun limitFieldAccess(newRootField: AccessorIdx): AccessNode? {
            var node = this
            while (true) {
                val accessor = node.accessor
                if (accessor == newRootField) return node.next
                if (accessor == ANY_ACCESSOR_IDX) return this
                node = node.next ?: return this
            }
        }

        companion object {
            @JvmStatic
            fun TreeApManager.createNodeFromAccessors(accessors: IntList): AccessNode? =
                accessors.foldRight(null as AccessNode?) { accessor, acc -> AccessNode(this, accessor, acc) }

            @JvmStatic
            fun TreeApManager.createNodeFromReversedAp(reversedAp: ReversedApNode?): AccessNode? =
                reversedAp.foldRight(null as AccessNode?) { accessor, acc -> AccessNode(this, accessor, acc) }

            class ReversedApNode(val accessor: AccessorIdx, val prev: ReversedApNode?)

            inline fun <R> ReversedApNode?.foldRight(
                initial: R, operation: (accessor: AccessorIdx, acc: R) -> R
            ): R {
                if (this == null) return initial

                var resultNode: R = initial
                var reversedNode: ReversedApNode = this

                while (true) {
                    val accessor = reversedNode.accessor
                    resultNode = operation(accessor, resultNode)
                    reversedNode = reversedNode.prev ?: return resultNode
                }
            }
        }
    }
}
