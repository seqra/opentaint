package org.opentaint.common.sast.sarif

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry.SourceStartEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind.CallToSink
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind.CallToSource
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralFullTraceNode
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

            if (rootNode !is InterProceduralFullTraceNode) {
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
    node: InterProceduralFullTraceNode
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
        if (successor !is InterProceduralFullTraceNode) {
            TODO("Start-2-source node is not full")
        }

        val successorIdx = getOrCreateNodeIdx(successor)

        root2SourceFwd.computeIfAbsent(nodeIdx, ::IntOpenHashSet).add(successorIdx)
        root2SourceBwd.computeIfAbsent(successorIdx, ::IntOpenHashSet).add(nodeIdx)

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
        is InterProceduralFullTraceNode -> node.trace.final
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

        root2SinkFwd.computeIfAbsent(nodeIdx, ::IntOpenHashSet).add(successorIdx)
        root2SinkBwd.computeIfAbsent(successorIdx, ::IntOpenHashSet).add(nodeIdx)

        traverseStartToSink(trace, visited, successorIdx, successor)
    }
}

private inline fun Iterable<InterProceduralTraceNode>.forEachNodeOrdered(body: (InterProceduralTraceNode) -> Unit) {
    sortedWith(NodeComparator).forEach { body(it) }
}

private object NodeComparator : Comparator<InterProceduralTraceNode> {
    override fun compare(
        a: InterProceduralTraceNode,
        b: InterProceduralTraceNode
    ): Int = when (a) {
        is InterProceduralSummaryTraceNode -> when (b) {
            is InterProceduralSummaryTraceNode -> SummaryNodeComparator.compare(a, b)
            is InterProceduralFullTraceNode -> -1
        }

        is InterProceduralFullTraceNode -> when (b) {
            is InterProceduralSummaryTraceNode -> 1
            is InterProceduralFullTraceNode -> FullNodeComparator.compare(a, b)
        }
    }
}

private object SummaryNodeComparator : Comparator<InterProceduralSummaryTraceNode> {
    override fun compare(
        a: InterProceduralSummaryTraceNode,
        b: InterProceduralSummaryTraceNode
    ): Int {
        MethodComparator.compare(a.trace.method, b.trace.method).let { if (it != 0) return it }
        a.trace.traceKind.compareTo(b.trace.traceKind).let { if (it != 0) return it }
        FinalEntryComparator.compare(a.trace.final, b.trace.final).let { if (it != 0) return it }
        return a.hashCode().compareTo(b.hashCode())
    }
}

private object FullNodeComparator : Comparator<InterProceduralFullTraceNode> {
    override fun compare(
        a: InterProceduralFullTraceNode,
        b: InterProceduralFullTraceNode
    ): Int {
        MethodComparator.compare(a.trace.method, b.trace.method).let { if (it != 0) return it }
        a.trace.traceKind.compareTo(b.trace.traceKind).let { if (it != 0) return it }
        FinalEntryComparator.compare(a.trace.final, b.trace.final).let { if (it != 0) return it }
        StartEntryComparator.compare(a.trace.startEntry, b.trace.startEntry).let { if (it != 0) return it }
        return a.hashCode().compareTo(b.hashCode())
    }
}

private object MethodComparator : Comparator<MethodEntryPoint> {
    override fun compare(a: MethodEntryPoint, b: MethodEntryPoint): Int =
        a.toString().compareTo(b.toString())
}

private object FinalEntryComparator : Comparator<TraceEntry.Final> {
    override fun compare(a: TraceEntry.Final, b: TraceEntry.Final): Int =
        a.toString().compareTo(b.toString())
}

private object StartEntryComparator : Comparator<TraceEntry.StartTraceEntry> {
    override fun compare(a: TraceEntry.StartTraceEntry, b: TraceEntry.StartTraceEntry): Int {
        return when (a) {
            is SourceStartEntry -> when (b) {
                is SourceStartEntry -> {
                    a.priority().compareTo(b.priority()).let { if (it != 0) return it }
                    a.toString().compareTo(b.toString())
                }

                is TraceEntry.MethodEntry -> -1
            }

            is TraceEntry.MethodEntry -> when (b) {
                is SourceStartEntry -> 1
                is TraceEntry.MethodEntry -> a.facts.toString().compareTo(b.facts.toString())
            }
        }
    }
}

private fun SourceStartEntry.priority(): Int {
    if (sourcePrimaryAction != null) return 2
    if (sourceOtherActions.any { it is TraceEntryAction.EntryPointSourceRule }) return 0
    if (sourceOtherActions.any { it is TraceEntryAction.CallSourceRule }) return 1
    return 3
}
