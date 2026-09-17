package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import java.util.concurrent.ConcurrentHashMap

class AccessTreeAnySuffixMatcher(suffixNode: AccessTree.AccessNode) {
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
                // disallowing [any]->...->[any]
                check(accessor != ANY_ACCESSOR_IDX)

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
     * The walk is a pure function of its three arguments: the trie is built once in `init` and never
     * touched again, and an [AccessTree.AccessNode] is immutable. A fact is a DAG, not a tree, so the
     * same pair is reached along many paths -- remembering the answer returns the answer the walk
     * would recompute.
     */
    private val walkMemo = ConcurrentHashMap<MemoKey, Any>()

    private class MemoKey(
        private val trie: Any,
        private val node: AccessTree.AccessNode,
        private val prefixCoveredByAny: Boolean,
    ) {
        override fun hashCode(): Int {
            var result = System.identityHashCode(trie)
            result = 31 * result + System.identityHashCode(node)
            return 31 * result + if (prefixCoveredByAny) 1 else 0
        }

        override fun equals(other: Any?): Boolean =
            other is MemoKey &&
                trie === other.trie &&
                node === other.node &&
                prefixCoveredByAny == other.prefixCoveredByAny
    }

    private object NoNode

    fun getNonMatchingNode(node: AccessTree.AccessNode) =
        getNonMatchingNode(root, node, true) ?: manager.emptyNode

    private fun getNonMatchingNode(trie: TrieNode, node: AccessTree.AccessNode, prefixCoveredByAny: Boolean): AccessTree.AccessNode? {
        val key = MemoKey(trie, node, prefixCoveredByAny)

        walkMemo[key]?.let { return if (it === NoNode) null else it as AccessTree.AccessNode }

        val result = computeNonMatchingNode(trie, node, prefixCoveredByAny)
        walkMemo[key] = result ?: NoNode
        return result
    }

    private fun computeNonMatchingNode(trie: TrieNode, node: AccessTree.AccessNode, prefixCoveredByAny: Boolean): AccessTree.AccessNode? {
        val accessorIdx = mutableListOf<AccessorIdx>()
        val accessorNodes = mutableListOf<AccessTree.AccessNode>()
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

        // all branches matched the any-suffix
        if (!node.isAbstract && !thisFinal && accessorIdx.isEmpty())
            return null

        // node is left unchanged
        if (!areChildrenChanged && thisFinal == node.isFinal)
            return node

        return manager.create(node.isAbstract, thisFinal, node.deepAccessorExclusion, accessorIdx.toIntArray(), accessorNodes.toTypedArray())
    }
}
