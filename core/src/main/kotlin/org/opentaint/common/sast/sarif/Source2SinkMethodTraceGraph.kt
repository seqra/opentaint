package org.opentaint.common.sast.sarif

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.ir.api.common.CommonMethod

class Source2SinkMethodTraceGraph {
    val allMethods = mutableListOf<CommonMethod>()
    val methodIndices = Object2IntOpenHashMap<CommonMethod>()

    fun getOrCreateMethodIdx(method: CommonMethod): Int =
        methodIndices.computeIfAbsent(method) {
            val idx = allMethods.size
            allMethods.add(method)
            idx
        }

    val sourceMethods = IntOpenHashSet()
    val sinkMethods = IntOpenHashSet()
    val rootMethods = IntOpenHashSet()

    val sink2RootMethodNodes = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val root2SourceMethodNodes = Int2ObjectOpenHashMap<IntOpenHashSet>()

    val sink2RootMethodEdges = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val root2SinkMethodEdges = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val root2SourceMethodEdges = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val source2RootMethodEdges = Int2ObjectOpenHashMap<IntOpenHashSet>()
}

class MethodTrace(val sink2Root: IntArray, val root2Source: IntArray)

fun Source2SinkTraceGraph.methodGraph(): Source2SinkMethodTraceGraph {
    val methodGraph = Source2SinkMethodTraceGraph()

    val visitedSinks = IntOpenHashSet()
    sinkNodes.forEachInt {
        val methodIdx = nodeMethodIdx(it, methodGraph)
        methodGraph.sinkMethods.add(methodIdx)

        methodGraphSink2Root(methodGraph, visitedSinks, it)
    }

    val reachableRoots = rootNodes.clone()
    reachableRoots.retainAll(visitedSinks)

    val visitedSources = IntOpenHashSet()
    reachableRoots.forEachInt {
        methodGraphRoot2Source(methodGraph, visitedSources, it)
    }

    return methodGraph
}

fun <T : Any> Source2SinkMethodTraceGraph.allMethodTraces(
    limit: Int?,
    collect: (MethodTrace) -> T?,
): List<T> {
    if (limit != null) require(limit >= 0) { "limit must be non-negative, was $limit" }
    val cap = limit ?: Int.MAX_VALUE
    if (cap == 0) return emptyList()

    return selectMethodTraces(
        methodCount = allMethods.size,
        sinkMethods = sinkMethods,
        rootMethods = rootMethods,
        sourceMethods = sourceMethods,
        sink2RootEdges = { sink2RootMethodEdges.get(it) },
        root2SourceEdges = { root2SourceMethodEdges.get(it) },
        forEachPredecessor = { node, action ->
            source2RootMethodEdges.get(node)?.forEachInt(action)
            root2SinkMethodEdges.get(node)?.forEachInt(action)
        },
        cap = cap,
        collect = collect,
    )
}

private fun Source2SinkTraceGraph.nodeMethodIdx(nodeIdx: Int, mg: Source2SinkMethodTraceGraph): Int {
    val node = allNodes[nodeIdx]
    val nodeMethod = node.methodEntryPoint.method
    return mg.getOrCreateMethodIdx(nodeMethod)
}

private fun Source2SinkTraceGraph.methodGraphSink2Root(
    mg: Source2SinkMethodTraceGraph,
    visited: IntOpenHashSet,
    nodeIdx: Int,
) {
    if (!visited.add(nodeIdx)) return

    val methodIdx = nodeMethodIdx(nodeIdx, mg)
    mg.sink2RootMethodNodes.computeIfAbsent(methodIdx) { IntOpenHashSet() }.add(nodeIdx)

    if (rootNodes.contains(nodeIdx)) {
        mg.rootMethods.add(methodIdx)
    }

    root2SinkBwd.get(nodeIdx)?.forEachInt { succIdx ->
        val succMethodIdx = nodeMethodIdx(succIdx, mg)
        mg.sink2RootMethodEdges.computeIfAbsent(methodIdx) { IntOpenHashSet() }.add(succMethodIdx)
        mg.root2SinkMethodEdges.computeIfAbsent(succMethodIdx) { IntOpenHashSet() }.add(methodIdx)

        methodGraphSink2Root(mg, visited, succIdx)
    }
}

private fun Source2SinkTraceGraph.methodGraphRoot2Source(
    mg: Source2SinkMethodTraceGraph,
    visited: IntOpenHashSet,
    nodeIdx: Int,
) {
    if (!visited.add(nodeIdx)) return

    val methodIdx = nodeMethodIdx(nodeIdx, mg)
    mg.root2SourceMethodNodes.computeIfAbsent(methodIdx) { IntOpenHashSet() }.add(nodeIdx)

    if (sourceNodes.contains(nodeIdx)) {
        mg.sourceMethods.add(methodIdx)
    }

    root2SourceFwd.get(nodeIdx)?.forEachInt { succIdx ->
        val succMethodIdx = nodeMethodIdx(succIdx, mg)
        mg.root2SourceMethodEdges.computeIfAbsent(methodIdx) { IntOpenHashSet() }.add(succMethodIdx)
        mg.source2RootMethodEdges.computeIfAbsent(succMethodIdx) { IntOpenHashSet() }.add(methodIdx)

        methodGraphRoot2Source(mg, visited, succIdx)
    }
}
