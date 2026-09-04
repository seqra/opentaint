package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.graph.IntGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo

internal object JIRAliasPathCompressor {
    fun compress(aliases: List<AliasInfo>, checkpoint: () -> Unit = {}): List<AliasInfo> {
        checkpoint()
        val result = LinkedHashSet<AliasInfo>()
        aliases.forEach { alias ->
            checkpoint()
            if (alias !is AliasApInfo || !alias.accessors.containsInvalidUnboundedPath()) {
                result += alias
            }
        }
        val accessorPaths = result.filterIsInstance<AliasApInfo>().filter { it.accessors.size >= 2 }
        if (accessorPaths.isEmpty()) return result.toList()

        val components = accessorPaths.connectedAccessorComponents(checkpoint)
        if (components.isEmpty()) return result.toList()

        // Dropping the whole permutation-bearing fact is intentional: a shortened path would be a new alias fact.
        return result.filterNot { alias ->
            checkpoint()
            alias is AliasApInfo && alias.accessors.containsAccessorPermutation(components)
        }
    }

    private fun List<AliasApInfo>.connectedAccessorComponents(
        checkpoint: () -> Unit,
    ): Map<AliasAccessor, Int> {
        val accessorIds = hashMapOf<AliasAccessor, Int>()
        val graph = IntGraph()

        fun accessorId(accessor: AliasAccessor): Int =
            accessorIds.getOrPut(accessor) { accessorIds.size }

        forEach { alias ->
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

    private fun List<AliasAccessor>.containsInvalidUnboundedPath(): Boolean {
        return zipWithNext().any { (outer, inner) ->
            outer is AliasAccessor.Array ||
                outer is AliasAccessor.Field && outer.fieldType == "java.lang.Object" ||
                inner is AliasAccessor.Field && inner.isErasedContainerAccessor() ||
                inner is AliasAccessor.Array &&
                (outer !is AliasAccessor.Field || !outer.fieldType.isArrayTypeName())
        }
    }

    private fun String.isArrayTypeName(): Boolean = endsWith("[]") || startsWith("[")

    private fun AliasAccessor.Field.isErasedContainerAccessor(): Boolean =
        fieldType == "java.lang.Object" &&
            fieldName in ERASED_CONTAINER_ACCESSOR_NAMES

    private const val NO_COMPONENT = -1
    private val ERASED_CONTAINER_ACCESSOR_NAMES = setOf("Element", "MapKey", "MapValue")
}
