package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.graph.DirectedMethodBlockLayout
import org.opentaint.dataflow.graph.MethodBlockLayout
import org.opentaint.dataflow.graph.MethodBlockRoute
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet
import java.util.Collections

/** A delivery frontier contains original statements or an exact block output edge. */
internal sealed interface BlockDeliveryTarget {
    data class Statement(val index: Int) : BlockDeliveryTarget
    data class Boundary(val route: MethodBlockRoute) : BlockDeliveryTarget
}

/**
 * One immutable layout, directed backend graph and lowest physical owner. Cache
 * the same neutral closure as CfgDeliveryCache, but make every outgoing block
 * edge a terminal control point. A cached search can never jump a loop gate.
 *
 * Boundary indexes below are private local cache points, never instructions or
 * LanguageManager indexes. No fact, rule, form or mutable current scope is kept.
 */
internal class BlockCfgDeliveryCache(
    private val layout: MethodBlockLayout,
    private val graph: CompactGraph,
    val block: BlockId,
    backward: Boolean,
    private val cancellation: Cancellation,
    directedView: DirectedMethodBlockLayout = layout.directed(graph, backward),
    boundaryTarget: (Int) -> Boolean = { false },
    relevant: (Int, AccessPathBase) -> Boolean,
) {
    private val points: List<BlockDeliveryTarget>
    private val boundaries: Map<Long, BlockDeliveryTarget.Boundary>
    private val cache: CfgDeliveryCache
    private val instructionCount = layout[block].instructions.size

    init {
        require(graph.size == layout.instructionCount)
        require(directedView.layout === layout && directedView.backward == backward)
        val allPoints = ArrayList<BlockDeliveryTarget>()
        for (index in layout[block].instructions) allPoints += BlockDeliveryTarget.Statement(index)
        val boundaryIndexes = HashMap<Long, Int>()
        val boundaryValues = HashMap<Long, BlockDeliveryTarget.Boundary>()
        for (from in layout[block].instructions) graph.forEachSuccessor(from) { to ->
            cancellation.checkpoint()
            val route = directedView.route(from, to)
            if (route.crossesBoundary || boundaryTarget(to)) {
                val edge = edgeKey(from, to)
                val value = BlockDeliveryTarget.Boundary(route)
                boundaryIndexes[edge] = allPoints.size
                boundaryValues[edge] = value
                allPoints += value
            }
        }
        points = Collections.unmodifiableList(allPoints)
        boundaries = Collections.unmodifiableMap(boundaryValues)
        val localGraph = CompactGraph.build(points.size) { point ->
            cancellation.checkpoint()
            BitSet(points.size).apply {
                val from = (points[point] as? BlockDeliveryTarget.Statement)?.index
                if (from != null) graph.forEachSuccessor(from) { to ->
                    val boundary = boundaryIndexes[edgeKey(from, to)]
                    if (boundary != null) set(boundary)
                    else {
                        check(layout.ownerOf(to) == block)
                        set(layout.localIndex(to))
                    }
                }
            }
        }
        cache = CfgDeliveryCache(localGraph, cancellation) { point, base ->
            when (val value = points[point]) {
                is BlockDeliveryTarget.Statement -> relevant(value.index, base)
                is BlockDeliveryTarget.Boundary -> true
            }
        }
    }

    val hits: Long get() = cache.hits
    val searches: Long get() = cache.searches
    /** Includes private boundary points; physical instruction diagnostics stay separate. */
    val visitedNodes: Long get() = cache.visitedNodes
    val destinations: Long get() = cache.destinations
    val maxWidth: Int get() = cache.maxWidth

    /** Include the given original statement when it is relevant. Empty is a cached answer. */
    fun targets(start: Int, base: AccessPathBase): List<BlockDeliveryTarget> {
        cancellation.checkpoint()
        require(layout.ownerOf(start) == block) { "Start $start is not owned by $block" }
        val local = layout.localIndex(start)
        check(local in 0 until instructionCount)
        // ZERO must execute each physical operation; it still meets explicit
        // boundary routing in after(), including self-loop feedback edges.
        if (base == AccessPathBase.Zero) return listOf(points[local])
        val indexes = cache.targets(local, base)
        if (indexes.isEmpty()) return emptyList()
        // Borrow the cached immutable index array. Do not allocate its members
        // again on a hit or store a second per-start/per-base frontier index.
        return object : AbstractList<BlockDeliveryTarget>() {
            override val size: Int get() = indexes.size
            override fun get(index: Int): BlockDeliveryTarget = points[indexes[index]]
        }
    }

    /** Called after processing and storing the result at the original statement. */
    fun after(from: Int, base: AccessPathBase): List<BlockDeliveryTarget> {
        cancellation.checkpoint()
        require(layout.ownerOf(from) == block) { "Source $from is not owned by $block" }
        val result = LinkedHashSet<BlockDeliveryTarget>()
        graph.forEachSuccessor(from) { to ->
            cancellation.checkpoint()
            val boundary = boundaries[edgeKey(from, to)]
            if (boundary != null) result += boundary else result += targets(to, base)
        }
        cancellation.checkpoint()
        return Collections.unmodifiableList(result.toList())
    }

    private fun edgeKey(from: Int, to: Int): Long =
        (from.toLong() shl 32) or (to.toLong() and 0xffffffffL)
}
