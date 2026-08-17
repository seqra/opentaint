package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.graph.IntGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo

internal object JIRAliasPathCompressor {
    fun compress(aliases: List<AliasInfo>, checkpoint: () -> Unit = {}): List<AliasInfo> {
        checkpoint()
        val result = LinkedHashSet(aliases)
        val components = result.toList().connectedAccessorComponents(checkpoint)
        if (components.isEmpty()) return result.toList()

        // Dropping the whole permutation-bearing fact is intentional: a shortened path would be a new alias fact.
        return result.filterNot { alias ->
            checkpoint()
            alias is AliasApInfo && alias.accessors.containsAccessorPermutation(components)
        }
    }

    private fun List<AliasInfo>.connectedAccessorComponents(
        checkpoint: () -> Unit,
    ): Map<AliasAccessor, Int> {
        val accessorIds = hashMapOf<AliasAccessor, Int>()
        val graph = IntGraph()

        fun accessorId(accessor: AliasAccessor): Int =
            accessorIds.getOrPut(accessor) { accessorIds.size }

        filterIsInstance<AliasApInfo>().forEach { alias ->
            checkpoint()
            alias.accessors.zipWithNext { outer, inner ->
                graph.addEdge(accessorId(outer), accessorId(inner))
            }
        }

        checkpoint()
        val components = graph.nonTrivialSccs().filter { it.cardinality() >= 2 }
        if (components.isEmpty()) return emptyMap()

        val componentByAccessorId = IntArray(accessorIds.size) { NO_COMPONENT }
        components.forEachIndexed { componentId, component ->
            checkpoint()
            var accessorId = component.nextSetBit(0)
            while (accessorId >= 0) {
                componentByAccessorId[accessorId] = componentId
                accessorId = component.nextSetBit(accessorId + 1)
            }
        }

        return accessorIds.mapValues { (_, accessorId) -> componentByAccessorId[accessorId] }
    }

    private fun List<AliasAccessor>.containsAccessorPermutation(
        componentByAccessor: Map<AliasAccessor, Int>,
    ): Boolean = zipWithNext().any { (outer, inner) ->
        val component = componentByAccessor[outer] ?: NO_COMPONENT
        component != NO_COMPONENT && component == componentByAccessor[inner]
    }

    private const val NO_COMPONENT = -1
}
