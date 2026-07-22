package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager

/**
 * Lazily materialize a grouped diagonal edge for a legacy flow operation. Both sides use the same
 * suffix cone, and both prefix/suffix seams are rebuilt through the existing field/element limiting
 * operations.
 */
fun Edge.FactToFact.materializeSuffixes(): List<Edge.FactToFact> {
    val bundle = suffixBundle ?: return listOf(this)
    val finalPrefixFact = factAp as? AccessTree
        ?: error("SuffixTree edge has a non-tree final prefix: ${factAp::class}")
    val manager = finalPrefixFact.access.manager

    return buildList {
        for (cone in bundle.suffixTree.cones()) {
            val exclusions = manager.exclusions(cone.exclusions)
            val initialAccess = manager.buildInitialPath(bundle.initialPrefix + cone.suffix)
            for (terminal in bundle.finalPrefixTree.terminals()) {
                val finalAccess = manager.buildFinalPath(
                    terminal.prefix + cone.suffix,
                    terminal.markers,
                ) ?: continue

                add(
                    Edge.FactToFact(
                        methodEntryPoint = methodEntryPoint,
                        initialFactAp = AccessPath(manager, initialFactAp.base, initialAccess, exclusions),
                        statement = statement,
                        factAp = AccessTree(manager, factAp.base, finalAccess, exclusions),
                    )
                )
            }
        }
    }
}

internal fun TreeApManager.buildInitialPath(accessors: List<Int>): AccessPath.AccessNode? {
    var node: AccessPath.AccessNode? = null
    for (index in accessors.indices.reversed()) {
        val accessor = accessors[index]
        node = if (node == null) {
            AccessPath.AccessNode(this, accessor, next = null)
        } else {
            node.addParent(accessor)
        }
    }
    return node
}

internal fun TreeApManager.buildFinalPath(
    accessors: List<Int>,
    markers: FinalPrefixMarkers,
): AccessTree.AccessNode? {
    var node = when {
        markers.isFinal && markers.isAbstract -> abstractFinalNode
        markers.isFinal -> finalNode
        markers.isAbstract -> abstractNode
        else -> emptyNode
    }
    for (index in accessors.indices.reversed()) {
        node = node.addParentIfPossible(accessors[index]) ?: return null
    }
    return node
}

internal fun TreeApManager.buildFinalPrefixTree(tree: FinalPrefixTree): AccessTree.AccessNode? {
    var result: AccessTree.AccessNode? = null
    for (terminal in tree.terminals()) {
        val branch = buildFinalPath(terminal.prefix, terminal.markers) ?: continue
        result = result?.mergeAdd(branch) ?: branch
    }
    return result
}

internal fun TreeApManager.exclusions(accessors: Set<Int>): ExclusionSet {
    var result: ExclusionSet = ExclusionSet.Empty
    for (accessor in accessors) result = result.add(with(this) { accessor.accessor })
    return result
}
