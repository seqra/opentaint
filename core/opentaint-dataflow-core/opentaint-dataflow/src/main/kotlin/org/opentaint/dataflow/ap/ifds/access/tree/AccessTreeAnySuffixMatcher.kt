package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor

class AccessTreeAnySuffixMatcher(suffixNode: AccessTree.AccessNode) {
    private val manager = suffixNode.manager
    private val root = TrieNode(isAbstract = false, isFinal = false, prefixLink = null, depth = 0)

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
            return "($abstraction$final, depth=$depth, $children)"
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
        this == ELEMENT_ACCESSOR_IDX || this.isFieldAccessor()

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
                    isAbstract = node.isAbstract || prefix.isAbstract,
                    isFinal = node.isFinal || prefix.isFinal,
                    prefix, depth
                )
                triePar.children.put(accessor, newTrieNode)

                node.forEachAccessor{ accessor, accessorNode ->
                    unprocessed.addLast(RawNodeWithParent(accessorNode, accessor, newTrieNode, depth + 1, curNotCoveredByAny))
                }
            }
        }
    }

    fun getNonMatchingNode(accessors: IntArray, nodes: Array<AccessTree.AccessNode>): Pair<IntArray, Array<AccessTree.AccessNode>> {
        val accessorIdx = mutableListOf<AccessorIdx>()
        val accessorNodes = mutableListOf<AccessTree.AccessNode>()

        accessors.forEachIndexed { i, accessor ->
            val accessorNode = nodes[i]
            val afterAny = root.children.get(accessor)
            val accessorCovered = accessor.coveredByAny()
            if (afterAny == null && !accessorCovered) {
                // two [any]-branches can be merged naturally, as those not accepted by [any]
                accessorIdx.add(accessor)
                accessorNodes.add(accessorNode)
            }
            else {
                val child = getNonMatchingNode(afterAny ?: root, accessorNode, accessorCovered)
                if (child != null) {
                    accessorIdx.add(accessor)
                    accessorNodes.add(child)
                }
            }
        }

        return accessorIdx.toIntArray() to accessorNodes.toTypedArray()
    }

    private fun getNonMatchingNode(trie: TrieNode, node: AccessTree.AccessNode, prefixCoveredByAny: Boolean): AccessTree.AccessNode? {
        val accessorIdx = mutableListOf<AccessorIdx>()
        val accessorNodes = mutableListOf<AccessTree.AccessNode>()

        node.forEachAccessor { accessor, accessorNode ->
            val prefixStillCovered = prefixCoveredByAny && (accessor == ANY_ACCESSOR_IDX || accessor.coveredByAny())
            // if prefix has an accessor not covered by [any], we cannot go back to root
            val fallback = if (prefixStillCovered) root else null
            val next = trie.findChild(accessor) ?: fallback
            if (next == null) {
                // fell out of suffix
                accessorIdx.add(accessor)
                accessorNodes.add(accessorNode)
            }
            val child = next?.let { getNonMatchingNode(it, accessorNode, prefixStillCovered) }
            if (child != null) {
                accessorIdx.add(accessor)
                accessorNodes.add(child)
            }
        }

        val thisAbstract = node.isAbstract && !trie.isAbstract
        val thisFinal = node.isFinal && !trie.isFinal

        // all branches matched the any-suffix
        if (!thisAbstract && !thisFinal && accessorIdx.isEmpty())
            return null

        return manager.create(thisAbstract, thisFinal, accessorIdx.toIntArray(), accessorNodes.toTypedArray())
    }
}
