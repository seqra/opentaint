package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.graph.IntGraph
import org.opentaint.dataflow.util.toIntSet
import java.util.BitSet
import java.util.IdentityHashMap

class MergingTreeSummaryStorage(val manager: TreeApManager) {
    private var edges: AccessNode? = null
    private var edgesDelta: AccessNode? = null

    fun add(exitAccess: AccessNode): Boolean {
        manager.cancellation.checkpoint()

        val currentEdges = edges

        val modifiedEdges = if (currentEdges == null) {
            exitAccess
        } else {
            currentEdges.mergeAdd(exitAccess, foldToAny = false)
        }

        var retainedEdges = modifiedEdges.absorbCoveredSiblings()

        if (retainedEdges.size > COMPRESSION_THRESHOLD) {
            val compressedEdges = manager.withAccessTreeInterner { interner, cache ->
                val currentInterned = retainedEdges.internNodes(interner, cache, global = true)
                val compressed = currentInterned.compressNode()

                if (compressed !== currentInterned) {
                    compressed.internNodes(interner, cache, global = true)
                } else null
            }
            if (compressedEdges != null) {
                retainedEdges = compressedEdges
            }
        }

        edges = retainedEdges
        val retainedDelta = if (currentEdges == null) {
            retainedEdges
        } else {
            currentEdges.mergeAddDelta(retainedEdges, foldToAny = false).second
        } ?: return false

        edgesDelta = edgesDelta?.mergeAdd(retainedDelta) ?: retainedDelta
        return true
    }

    fun edges(): AccessNode? = edges

    fun getAndResetDelta(): AccessNode? {
        val delta = edgesDelta ?: return null
        edgesDelta = null

        return manager.withAccessTreeInterner { interner, cache ->
            edges = edges?.internNodes(interner, cache, global = true)
            delta.internNodes(interner, cache, global = true)
        }
    }

    private fun AccessNode.compressNode(): AccessNode {
        val components = connectedAccessorComponents()

        var result = this
        for (component in components) {
            if (component.cardinality() < 2) continue

            result = result.removeAllAccessorChains(
                component.toIntSet(), chainLengthToRemove = 2, IdentityHashMap(), manager.cancellation
            )
        }
        if (this === result) return this

        return result.compressNode()
    }

    private fun AccessNode.connectedAccessorComponents(): List<BitSet> {
        val graph = IntGraph()
        buildAccessorGraph(graph, IdentityHashMap())
        return graph.nonTrivialSccs()
    }

    private fun AccessNode.buildAccessorGraph(graph: IntGraph, visited: IdentityHashMap<AccessNode, Unit>) {
        if (visited.put(this, Unit) != null) return

        forEachAccessor { outer, node ->
            node.forEachAccessor { inner, _ ->
                graph.addEdge(outer, inner)
            }
            node.buildAccessorGraph(graph, visited)
        }
    }

    companion object {
        private const val COMPRESSION_THRESHOLD = 100
    }
}
