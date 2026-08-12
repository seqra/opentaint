package org.opentaint.dataflow.ap.ifds.trace.path

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry.SourceStartEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind.CallToSink
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind.CallToSource
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralStart2FinalTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralSummaryTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.SourceToSinkTrace

class Source2SinkTraceGraph {
    val allNodes = mutableListOf<InterProceduralTraceNode>()
    val nodeIndices = Object2IntOpenHashMap<InterProceduralTraceNode>()

    val sourceNodes = IntOpenHashSet()
    val sinkNodes = IntOpenHashSet()
    val rootNodes = IntOpenHashSet()
    val root2SourceFwd = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val root2SourceBwd = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val root2SinkFwd = Int2ObjectOpenHashMap<IntOpenHashSet>()
    val root2SinkBwd = Int2ObjectOpenHashMap<IntOpenHashSet>()

    fun getOrCreateNodeIdx(node: InterProceduralTraceNode): Int =
        nodeIndices.computeIfAbsent(node) {
            val idx = allNodes.size
            allNodes.add(node)
            idx
        }
}

fun createSource2SinkGraph(trace: SourceToSinkTrace): Source2SinkTraceGraph {
    val graph = Source2SinkTraceGraph()
    val visitedSource = IntOpenHashSet()
    val visitedSink = IntOpenHashSet()

    trace.startNodes
        .filterIsInstance<InterProceduralTraceNode>()
        .forEachNodeOrdered { rootNode ->
            val rootIdx = graph.getOrCreateNodeIdx(rootNode)

            if (rootNode !is InterProceduralStart2FinalTraceNode) {
                TODO("Root node is not full")
            }

            graph.traverseStart2Source(trace, visitedSource, rootIdx, rootNode)
            graph.traverseStartToSink(trace, visitedSink, rootIdx, rootNode)
        }

    graph.rootNodes.addAll(graph.root2SinkFwd.keys)
    graph.rootNodes.addAll(graph.sinkNodes)

    val allSourceNodes = graph.sourceNodes.clone()
    allSourceNodes.addAll(graph.root2SourceFwd.keys)

    graph.rootNodes.retainAll(allSourceNodes)
    return graph
}

private fun Source2SinkTraceGraph.traverseStart2Source(
    trace: SourceToSinkTrace,
    visited: IntOpenHashSet,
    nodeIdx: Int,
    node: InterProceduralStart2FinalTraceNode
) {
    if (!visited.add(nodeIdx)) return

    val sourceStart = node.trace.startEntry as? SourceStartEntry

    val sourceStartSummary = sourceStart?.sourcePrimaryAction as? TraceEntryAction.CallSourceSummary
    if (sourceStartSummary == null) {
        sourceNodes.add(nodeIdx)
        return
    }

    val sourceSuccessors = trace.findSuccessors(
        node, kind = CallToSource, sourceStart.statement, sourceStartSummary.summaryTrace
    )
    if (sourceSuccessors.isEmpty()) {
        // todo: fix trace
        return
    }

    sourceSuccessors.map { it.node }.forEachNodeOrdered { successor ->
        if (successor !is InterProceduralStart2FinalTraceNode) {
            TODO("Start-2-source node is not full")
        }

        val successorIdx = getOrCreateNodeIdx(successor)

        root2SourceFwd.computeIfAbsent(nodeIdx) { IntOpenHashSet() }.add(successorIdx)
        root2SourceBwd.computeIfAbsent(successorIdx) { IntOpenHashSet() }.add(nodeIdx)

        traverseStart2Source(trace, visited, successorIdx, successor)
    }
}

private fun Source2SinkTraceGraph.traverseStartToSink(
    trace: SourceToSinkTrace,
    visited: IntOpenHashSet,
    nodeIdx: Int,
    node: InterProceduralTraceNode
) {
    if (!visited.add(nodeIdx)) return

    if (node in trace.sinkNodes) {
        sinkNodes.add(nodeIdx)
        return
    }

    val finalEntry = when (node) {
        is InterProceduralStart2FinalTraceNode -> node.trace.final
        is InterProceduralSummaryTraceNode -> node.trace.final
    }

    val lastStatement = finalEntry.statement
    val sinkSuccessors = trace.findSuccessors(node, kind = CallToSink, lastStatement)
    if (sinkSuccessors.isEmpty()) {
        // todo: fix trace
        return
    }

    sinkSuccessors.map { it.node }.forEachNodeOrdered { successor ->
        val successorIdx = getOrCreateNodeIdx(successor)

        root2SinkFwd.computeIfAbsent(nodeIdx) { IntOpenHashSet() }.add(successorIdx)
        root2SinkBwd.computeIfAbsent(successorIdx) { IntOpenHashSet() }.add(nodeIdx)

        traverseStartToSink(trace, visited, successorIdx, successor)
    }
}

private inline fun Iterable<InterProceduralTraceNode>.forEachNodeOrdered(body: (InterProceduralTraceNode) -> Unit) {
    sortedWith(NodeComparator).forEach { body(it) }
}
