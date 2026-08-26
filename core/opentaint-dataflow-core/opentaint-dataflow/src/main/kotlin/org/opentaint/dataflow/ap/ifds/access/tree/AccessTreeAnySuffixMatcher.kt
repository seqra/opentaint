package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX

class AccessTreeAnySuffixMatcher(suffixNode: AccessTree.AccessNode) {
    companion object {
        /**
         * `-Dopentaint.anyTrimAbstract=true`, default **false**.
         *
         * The trim cancels `isFinal` and does not cancel `isAbstract`. With this on it cancels both,
         * so `[any].*` subsumes a sibling `f.*` for covered `f` -- which it denotes, so the deletion
         * is exact and not even a coarsening.
         *
         * OFF by default because it is a denotation change on the operator every storage channel's
         * merge runs, and because it removes the abstract nodes that are the graft points: the
         * counterfactual counts 2.2 BILLION single-node branches kept only by the missing clause on
         * the frontier arm, so the blast radius is large in both directions.
         */
        @JvmField
        val TRIM_ABSTRACT: Boolean =
            System.getProperty("opentaint.anyTrimAbstract")?.trim().toBoolean()
    }

    private val manager = suffixNode.manager
    private val root = TrieNode(suffixNode.isAbstract, suffixNode.isFinal, prefixLink = null, depth = 0)

    private data class TrieNode(
        val isAbstract: Boolean,
        val isFinal: Boolean,
        val prefixLink: TrieNode?,
        val depth: Int,
        val children: Int2ObjectOpenHashMap<TrieNode> = Int2ObjectOpenHashMap<TrieNode>()
    ) {
        fun findChild(accessor: Int): TrieNode? {
            val child = children.get(accessor)
            if (child != null)
                return child
            return prefixLink?.findChild(accessor)
        }

        override fun toString(): String {
            val abstraction = if (isAbstract) "A" else ""
            val final = if (isFinal) "F" else ""
            val sep = if (isAbstract || isFinal) ", " else ""
            return "($abstraction$final${sep}depth=$depth, $children)"
        }

        override fun equals(other: Any?): Boolean {
            if (other !is TrieNode)
                return false
            if (this === other)
                return true
            if (prefixLink !== other.prefixLink)
                return false
            if (isAbstract != other.isAbstract || isFinal != other.isFinal || depth != other.depth)
                return false
            return children == other.children
        }

        override fun hashCode(): Int {
            var result = 31 * depth
            if (isAbstract) result += 17
            if (isFinal) result += 13
            return result * 31 + children.hashCode()
        }
    }

    private fun AccessorIdx.coveredByAny(): Boolean =
        manager.isCoveredByAny(this)

    private data class RawNodeWithParent(
        val node: AccessTree.AccessNode,
        val accessor: AccessorIdx,
        val parent: TrieNode,
        val depth: Int,
        val notCoveredByAny: Int?,
    )

    init {
        if (suffixNode.accessors != null && suffixNode.accessorNodes != null) {
            val unprocessed = ArrayDeque<RawNodeWithParent>()
            suffixNode.forEachAccessor { accessor, accessorNode ->
                val notCoveredByAny = if (accessor.coveredByAny()) null else 1
                unprocessed.addLast(RawNodeWithParent(accessorNode, accessor, root, 1, notCoveredByAny))
            }

            while (unprocessed.isNotEmpty()) {
                val (node, accessor, triePar, depth, notCoveredByAny) = unprocessed.removeFirst()

                if (accessor == ANY_ACCESSOR_IDX) {
                    // `[any]` is ZERO OR MORE covered steps, so `[any].<covered>*.[any]` == `[any]`.
                    // Absorb the nested one instead of rejecting it: re-enqueue its children at the
                    // SAME trie parent, depth and notCoveredByAny as the `[any]` node itself, which
                    // is exactly the suffix language the outer `[any]` already denotes.
                    node.forEachAccessor { childAccessor, childNode ->
                        unprocessed.addLast(
                            RawNodeWithParent(childNode, childAccessor, triePar, depth, notCoveredByAny)
                        )
                    }
                    continue
                }

                val curNotCoveredByAny = when {
                    notCoveredByAny != null -> notCoveredByAny
                    !accessor.coveredByAny() -> depth
                    else -> null
                }

                var prefix = triePar.prefixLink
                while (prefix != null) {
                    val next = prefix.children.get(accessor)
                    if (next != null) {
                        val notCoveredStillInSuffix = curNotCoveredByAny == null || depth - next.depth < curNotCoveredByAny
                        prefix = if (notCoveredStillInSuffix) next else null
                        break
                    }
                    prefix = prefix.prefixLink
                }
                if (triePar === root) {
                    prefix = root
                }
                if (prefix == null) {
                    prefix = root.children.get(accessor) ?: root
                }
                val newTrieNode = TrieNode(
                    isAbstract = node.isAbstract,
                    isFinal = node.isFinal || prefix.isFinal,
                    prefix, depth
                )
                triePar.children.put(accessor, newTrieNode)

                node.forEachAccessor { accessor, accessorNode ->
                    unprocessed.addLast(RawNodeWithParent(accessorNode, accessor, newTrieNode, depth + 1, curNotCoveredByAny))
                }
            }
        }
    }

    /**
     * Memo for ONE walk, keyed on `(trie, node)` per value of `prefixCoveredByAny`.
     *
     * The walk is a pure function of those three, and a fact is a DAG rather than a tree, so without
     * a memo a shared subtree is re-derived once per path that reaches it. Identity keys throughout:
     * `AccessNode.equals` is a deep structural comparison and `TrieNode` is a data class holding a
     * child map, so value equality here would cost more than the walk it saves.
     *
     * Profiled 2026-08-26: `getNonMatchingNode` was **73.6% of all analyser CPU and 83.5% of all
     * allocation** in the late window of the conductor arm, against 0 of 3,440 samples in the first
     * 60 s. Nothing else in the engine grew superlinearly with fact size.
     */
    private val memoCovered = java.util.IdentityHashMap<TrieNode, java.util.IdentityHashMap<AccessTree.AccessNode, Any>>()
    private val memoUncovered = java.util.IdentityHashMap<TrieNode, java.util.IdentityHashMap<AccessTree.AccessNode, Any>>()

    private object Dropped

    fun getNonMatchingNode(node: AccessTree.AccessNode) =
        getNonMatchingNode(root, node, true) ?: manager.emptyNode

    private fun getNonMatchingNode(
        trie: TrieNode,
        node: AccessTree.AccessNode,
        prefixCoveredByAny: Boolean,
    ): AccessTree.AccessNode? {
        val memo = (if (prefixCoveredByAny) memoCovered else memoUncovered)
            .getOrPut(trie) { java.util.IdentityHashMap() }

        val cached = memo[node]
        if (cached != null) {
            if (ApOpDiagnostics.enabled) ApOpDiagnostics.trimMemoHits.incrementAndGet()
            @Suppress("UNCHECKED_CAST")
            return if (cached === Dropped) null else cached as AccessTree.AccessNode
        }
        if (ApOpDiagnostics.enabled) ApOpDiagnostics.trimMemoMisses.incrementAndGet()

        val result = computeNonMatchingNode(trie, node, prefixCoveredByAny)
        memo[node] = result ?: Dropped
        return result
    }

    private fun computeNonMatchingNode(trie: TrieNode, node: AccessTree.AccessNode, prefixCoveredByAny: Boolean): AccessTree.AccessNode? {
        // Presized and unboxed. These two lines were 45.8% of the whole run's allocation as
        // `mutableListOf`: an `ArrayList<Int>` boxes every accessor index, and both lists grew from
        // the default capacity on a walk that visits every node of the tree.
        val width = node.accessors?.size ?: 0
        val accessorIdx = IntArrayList(width)
        val accessorNodes = ArrayList<AccessTree.AccessNode>(width)
        var areChildrenChanged = false

        node.forEachAccessor { accessor, accessorNode ->
            val prefixStillCovered = prefixCoveredByAny && (accessor == ANY_ACCESSOR_IDX || accessor.coveredByAny())
            // if prefix has an accessor not covered by [any], we cannot go back to root
            val fallback = if (prefixStillCovered) root else null
            val next = trie.findChild(accessor) ?: fallback
            if (next == null) {
                // fell out of suffix
                accessorIdx.add(accessor)
                accessorNodes.add(accessorNode)
                return@forEachAccessor
            }
            val child = getNonMatchingNode(next, accessorNode, prefixStillCovered)
            if (child != accessorNode)
                areChildrenChanged = true
            if (child != null) {
                accessorIdx.add(accessor)
                accessorNodes.add(child)
            }
        }

        val thisFinal = node.isFinal && !trie.isFinal

        // The trim cancels `isFinal` and does NOT cancel `isAbstract`: there is no
        // `thisAbstract = node.isAbstract && !trie.isAbstract` to mirror `thisFinal`, and the rebuild
        // below passes `node.isAbstract` through unchanged. So `[any].*` does not subsume a sibling
        // `f.*` whose node is abstract, even though it denotes a superset.
        //
        // Abstract nodes are exactly the graft points, and graft points per concat call is the
        // quantity that runs away on conductor (15.7 -> 109.1 between the early and late windows).
        // MEASURED HERE, NOT FIXED HERE: completing the predicate is a denotation change, and the
        // matcher is used by the merge on every storage channel.
        if (ApOpDiagnostics.enabled && node.isAbstract && trie.isAbstract && !thisFinal && accessorIdx.isEmpty()) {
            ApOpDiagnostics.trimKeptForAbstract.incrementAndGet()
            ApOpDiagnostics.trimKeptForAbstractNodes.addAndGet(node.size)
        }

        val thisAbstract = if (TRIM_ABSTRACT) node.isAbstract && !trie.isAbstract else node.isAbstract

        // all branches matched the any-suffix
        if (!thisAbstract && !thisFinal && accessorIdx.isEmpty())
            return null

        // node is left unchanged
        if (!areChildrenChanged && thisFinal == node.isFinal && thisAbstract == node.isAbstract)
            return node

        // Only ever DROPS branches and rebuilds under the same accessors, so the node's own `[any]`
        // state carries across -- and is dropped automatically when the trim removed that edge.
        return node.recreate(thisAbstract, thisFinal, node.deepAccessorExclusion, accessorIdx.toIntArray(), accessorNodes.toTypedArray())
    }
}
