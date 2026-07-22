package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessBasedStorage
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTreeSoftInterner
import org.opentaint.dataflow.ap.ifds.access.tree.SUMMARY_TREE_COMPRESSION_THRESHOLD
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.access.tree.compressSummaryCycles

/**
 * Reproduces Tree summary canonicalization that is orthogonal to diagonal suffix factoring.
 *
 * For one pair of bases/exit point, Tree summaries split the conclusion branch equal to the
 * premise into their identity index. All remaining conclusion branches for an exact materialized
 * premise are unioned, while their root exclusions are intersected. The resulting generalized
 * branches are fed back into [SuffixRelationTrie]; downstream storage remains suffix-native.
 *
 * Retaining only the merged final-prefix state per non-identity premise is substantially smaller
 * than retaining a complete second Tree summary store (including its premise tries, identity
 * index, builders, and cell hierarchy). The state reuses Tree's large-tree cycle compressor, but
 * all states in this cell share one soft interner rather than allocating an interner per premise.
 */
internal class FinalSideSummaryCanonicalizer(
    private val relation: SuffixRelationTrie,
    private val manager: TreeApManager,
) {
    private data class State(
        var finalAccess: AccessTree.AccessNode,
        var exclusions: Set<Int>,
    )

    private class InitialStorage(
        manager: TreeApManager,
    ) : AccessBasedStorage<InitialStorage>(manager) {
        var state: State? = null

        override fun createStorage(): InitialStorage = InitialStorage(manager)

        override fun printStorageNode(): String = state.toString()
    }

    private val nonIdentityByInitial = InitialStorage(manager)
    private val finalAccessInterner = AccessTreeSoftInterner(manager)

    /** Returns the canonical Tree-style generators whose language was newly generalized. */
    fun add(
        initialAccess: AccessPath.AccessNode?,
        finalAccess: AccessTree.AccessNode,
        exclusions: Set<Int>,
    ): List<SuffixGenerator> {
        val initialPath = initialAccess.toAccessorList()
        val result = ArrayList<SuffixGenerator>()

        val nonIdentity = when (val match = finalAccess.splitOnMatching(initialAccess)) {
            AccessTree.AccessNode.MatchResult.NotMatched -> finalAccess
            is AccessTree.AccessNode.MatchResult.MatchedWithRemainder -> {
                val identity = relation.factor(
                    initialPath.toIntArray(),
                    initialPath.toIntArray(),
                    exclusions,
                    FinalPrefixMarkers(isFinal = false, isAbstract = true),
                )
                if (relation.add(identity)) result.add(identity)
                match.remainder
            }
        } ?: return result

        val storage = nonIdentityByInitial.getOrCreateNode(initialAccess)
        val state = storage.state
        val delta: AccessTree.AccessNode
        val mergedExclusions: Set<Int>
        if (state == null) {
            mergedExclusions = exclusions.toSet()
            val (storedFinal, storedDelta) = compressIfRequired(nonIdentity, nonIdentity)
            storage.state = State(storedFinal, mergedExclusions)
            delta = checkNotNull(storedDelta)
        } else {
            val previousExclusions = state.exclusions
            mergedExclusions = previousExclusions.intersect(exclusions)
            val exclusionsWidened = mergedExclusions != previousExclusions
            val (mergedFinal, treeDelta) = state.finalAccess.mergeAddDelta(nonIdentity)
            val (storedFinal, storedDelta) = compressIfRequired(mergedFinal, treeDelta)
            state.finalAccess = storedFinal
            state.exclusions = mergedExclusions

            // A wider root exclusion applies to every retained branch, so all of them are delta.
            delta = if (exclusionsWidened) {
                storedFinal
            } else {
                storedDelta ?: return result
            }
        }

        for (terminal in delta.terminals()) {
            val generator = relation.factor(
                initialPath.toIntArray(),
                terminal.accessors.toIntArray(),
                mergedExclusions,
                terminal.markers,
            )
            if (relation.add(generator)) result.add(generator)
        }
        return result
    }

    /** Apply Tree's scale-only cycle abstraction without a merging-store wrapper per premise. */
    private fun compressIfRequired(
        finalAccess: AccessTree.AccessNode,
        delta: AccessTree.AccessNode?,
    ): Pair<AccessTree.AccessNode, AccessTree.AccessNode?> {
        if (finalAccess.size <= SUMMARY_TREE_COMPRESSION_THRESHOLD) return finalAccess to delta

        return finalAccessInterner.withInterner { interner, cache ->
            val interned = finalAccess.internNodes(interner, cache)
            val compressed = interned.compressSummaryCycles(manager)
            if (compressed === interned) {
                finalAccess to delta
            } else {
                val internedCompressed = compressed.internNodes(interner, cache)
                internedCompressed to internedCompressed
            }
        }
    }

    private data class Terminal(
        val accessors: List<Int>,
        val markers: FinalPrefixMarkers,
    )

    private fun AccessTree.AccessNode.terminals(): List<Terminal> = buildList {
        val path = ArrayList<Int>()
        fun visit(node: AccessTree.AccessNode) {
            if (node.isFinal || node.isAbstract) {
                add(Terminal(path.toList(), FinalPrefixMarkers(node.isFinal, node.isAbstract)))
            }
            node.forEachAccessor { accessor, child ->
                path.add(accessor)
                visit(child)
                path.removeAt(path.lastIndex)
            }
        }
        visit(this@terminals)
    }

    private fun AccessPath.AccessNode?.toAccessorList(): List<Int> {
        if (this == null) return emptyList()
        val values = toList()
        return List(values.size) { values.getInt(it) }
    }
}
