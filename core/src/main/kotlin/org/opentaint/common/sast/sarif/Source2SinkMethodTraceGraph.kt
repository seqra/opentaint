package org.opentaint.common.sast.sarif

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
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
    val root2SourceMethodEdges = Int2ObjectOpenHashMap<IntOpenHashSet>()
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

    val result = mutableListOf<T>()
    val coveredNodes = IntOpenHashSet()

    val sourcesFromRootCache = Int2ObjectOpenHashMap<IntOpenHashSet>()
    fun sourcesFromRoot(root: Int): IntOpenHashSet =
        sourcesFromRootCache.computeIfAbsent(root) {
            val reached = reachableNodes(root) { root2SourceMethodEdges.get(it) }
            val sources = sourceMethods.clone()
            sources.retainAll(reached)
            sources
        }

    val sourcesFromSinkCache = Int2ObjectOpenHashMap<IntOpenHashSet>()
    fun reachableSourcesFromSink(sink: Int): IntOpenHashSet =
        sourcesFromSinkCache.computeIfAbsent(sink) {
            val roots = reachableNodes(sink) { sink2RootMethodEdges.get(it) }
            val sources = IntOpenHashSet()
            roots.forEachInt { r ->
                if (rootMethods.contains(r)) sourcesFromRoot(r).forEachInt { sources.add(it) }
            }
            sources
        }

    forEachSourceSinkTrace(result, cap, coveredNodes, ::reachableSourcesFromSink, ::sourcesFromRoot, stop = { true }) {
        collect(it)
    }

    forEachSourceSinkTrace(
        result,
        cap,
        coveredNodes,
        ::reachableSourcesFromSink,
        ::sourcesFromRoot,
        stop = { result.size >= cap }) { candidate ->
        var addsNewNode = false
        candidate.forEachNode { if (!coveredNodes.contains(it)) addsNewNode = true }
        if (!addsNewNode) return@forEachSourceSinkTrace null

        collect(candidate)
    }

    return result
}

private inline fun MethodTrace.forEachNode(action: (Int) -> Unit) {
    for (m in sink2Root) action(m)
    for (element in root2Source) action(element)
}

private fun <T : Any> Source2SinkMethodTraceGraph.forEachSourceSinkTrace(
    result: MutableList<T>,
    cap: Int,
    coveredNodes: IntOpenHashSet,
    reachableSourcesFromSink: (Int) -> IntOpenHashSet,
    sourcesFromRoot: (Int) -> IntOpenHashSet,
    stop: () -> Boolean,
    collect: (MethodTrace) -> T?
) {
    val sinkIter = sinkMethods.intIterator()
    while (sinkIter.hasNext() && result.size < cap) {
        val sink = sinkIter.nextInt()
        val sourceIter = reachableSourcesFromSink(sink).intIterator()
        while (sourceIter.hasNext() && result.size < cap) {
            val source = sourceIter.nextInt()
            forEachMethodTrace(sink, source, { r -> sourcesFromRoot(r) }) { candidate ->
                val res = collect(candidate)
                    ?: return@forEachMethodTrace false

                result.add(res)
                candidate.forEachNode { coveredNodes.add(it) }
                stop()
            }
        }
    }
}

private fun Source2SinkMethodTraceGraph.forEachMethodTrace(
    sink: Int,
    source: Int,
    sourcesFromRoot: (Int) -> IntOpenHashSet,
    onTrace: (MethodTrace) -> Boolean,
): Boolean {
    val sinkVisited = IntOpenHashSet()
    val sinkPath = IntArrayList()
    return dfsSimplePaths(
        sink, sinkVisited, sinkPath,
        isFinal = { rootMethods.contains(it) },
        successors = { sink2RootMethodEdges.get(it) },
    ) { sink2RootPath ->
        val root = sink2RootPath.getInt(sink2RootPath.lastIndex)
        if (!sourcesFromRoot(root).contains(source)) {
            return@dfsSimplePaths false
        }

        val sink2Root = sink2RootPath.toIntArray()
        val srcVisited = IntOpenHashSet()
        val srcPath = IntArrayList()
        dfsSimplePaths(
            root, srcVisited, srcPath,
            isFinal = { it == source },
            successors = { root2SourceMethodEdges.get(it) },
        ) { root2SourcePath ->
            onTrace(MethodTrace(sink2Root, root2SourcePath.toIntArray()))
        }
    }
}

private fun dfsSimplePaths(
    start: Int,
    visited: IntOpenHashSet,
    path: IntArrayList,
    isFinal: (Int) -> Boolean,
    successors: (Int) -> IntOpenHashSet?,
    onPath: (IntArrayList) -> Boolean,
): Boolean {
    if (!visited.add(start)) return false
    path.add(start)

    try {
        if (isFinal(start)) {
            if (onPath(path)) return true
        }

        successors(start)?.forEachInt { next ->
            if (dfsSimplePaths(next, visited, path, isFinal, successors, onPath)) {
                return true
            }
        }

        return false
    } finally {
        path.removeInt(path.lastIndex)
        visited.remove(start)
    }
}

private fun reachableNodes(start: Int, successors: (Int) -> IntOpenHashSet?): IntOpenHashSet {
    val visited = IntOpenHashSet()
    val unprocessed = IntArrayList()
    unprocessed.add(start)

    while (unprocessed.isNotEmpty()) {
        val node = unprocessed.removeInt(unprocessed.lastIndex)
        if (!visited.add(node)) continue
        successors(node)?.let { unprocessed.addAll(it) }
    }

    return visited
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
    mg.sink2RootMethodNodes.computeIfAbsent(methodIdx, ::IntOpenHashSet).add(nodeIdx)

    if (rootNodes.contains(nodeIdx)) {
        mg.rootMethods.add(methodIdx)
    }

    root2SinkBwd.get(nodeIdx)?.forEachInt { succIdx ->
        val succMethodIdx = nodeMethodIdx(succIdx, mg)
        mg.sink2RootMethodEdges.computeIfAbsent(methodIdx, ::IntOpenHashSet).add(succMethodIdx)

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
    mg.root2SourceMethodNodes.computeIfAbsent(methodIdx, ::IntOpenHashSet).add(nodeIdx)

    if (sourceNodes.contains(nodeIdx)) {
        mg.sourceMethods.add(methodIdx)
    }

    root2SourceFwd.get(nodeIdx)?.forEachInt { succIdx ->
        val succMethodIdx = nodeMethodIdx(succIdx, mg)
        mg.root2SourceMethodEdges.computeIfAbsent(methodIdx, ::IntOpenHashSet).add(succMethodIdx)

        methodGraphRoot2Source(mg, visited, succIdx)
    }
}
