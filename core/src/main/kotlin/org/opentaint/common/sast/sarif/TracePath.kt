package org.opentaint.common.sast.sarif

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import kotlinx.collections.immutable.PersistentList
import kotlinx.collections.immutable.persistentListOf
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.CallKind.CallInnerTrace
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralFullTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.InterProceduralTraceNode
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.SourceToSinkTrace
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.ir.api.common.cfg.CommonInst

private val logger = object : KLogging() {}.logger

sealed interface TracePathGenerationResult {
    data class Path(val path: List<List<TracePathNode>>) : TracePathGenerationResult
    data object Simple : TracePathGenerationResult
    data object Failure : TracePathGenerationResult
}

fun generateTracePath(trace: TraceResolver.Trace, limit: Int?): TracePathGenerationResult {
    try {
        val sourceToSinkTrace = trace.sourceToSinkTrace
        val startNodes = sourceToSinkTrace.startNodes
        if (startNodes.isEmpty()) {
            logger.error { "Trace has no start nodes" }
            return TracePathGenerationResult.Failure
        }

        val singleNode = startNodes.singleOrNull()
        if (singleNode != null && singleNode is TraceResolver.SimpleTraceNode) {
            // trace has no additional info
            return TracePathGenerationResult.Simple
        }

        val nodeTraces = enumerateTraces(sourceToSinkTrace, limit)
        val resolvedPaths = nodeTraces.mapNotNull { generateSourceToSinkPath(sourceToSinkTrace, it) }

        if (resolvedPaths.isEmpty()) {
            logger.error { "Trace has no resolved paths" }
            return TracePathGenerationResult.Failure
        }

        return TracePathGenerationResult.Path(resolvedPaths)
    } catch (ex: Throwable) {
        logger.error(ex) { "Failed to generate trace path" }
        return TracePathGenerationResult.Failure
    }
}

private class NodeTrace(val sink2Root: IntArray, val root2Source: IntArray)

private class ResolvedNodeTrace(
    val root2Source: List<InterProceduralTraceNode>,
    val root2SinkNoRoot: List<InterProceduralTraceNode>,
)

private fun enumerateTraces(trace: SourceToSinkTrace, limit: Int?): List<ResolvedNodeTrace> {
    val graph = createSource2SinkGraph(trace)

    val methodGraph = graph.methodGraph()
    val nodeTraces = methodGraph.allMethodTraces(limit) {
        graph.processMethodTrace(methodGraph, it)
    }

    return nodeTraces.map { graph.resolvedNodeTrace(it) }
}

private fun Source2SinkTraceGraph.resolvedNodeTrace(trace: NodeTrace): ResolvedNodeTrace {
    val root2Source = trace.root2Source.map { allNodes[it] }
    val root2Sink = trace.sink2Root.map { allNodes[it] }.reversed()
    return ResolvedNodeTrace(root2Source, root2Sink)
}

private fun Source2SinkTraceGraph.processMethodTrace(
    mg: Source2SinkMethodTraceGraph,
    trace: MethodTrace
): NodeTrace? {
    val result = NodeTrace(IntArray(trace.sink2Root.size), IntArray(trace.root2Source.size))
    val sinkMethod = trace.sink2Root[0]
    mg.sink2RootMethodNodes.get(sinkMethod)?.forEachInt { node ->
        result.sink2Root[0] = node
        processMethodTrace(
            1,
            trace.sink2Root,
            result.sink2Root,
            { mg.sink2RootMethodNodes.get(it) },
            { root2SinkBwd.get(it) }
        ) {
            result.root2Source[0] = result.sink2Root.last()
            processMethodTrace(
                1,
                trace.root2Source,
                result.root2Source,
                { mg.root2SourceMethodNodes.get(it) },
                { root2SourceFwd.get(it) }
            ) { result }
        }?.let { return it }
    }
    return null
}

private fun processMethodTrace(
    i: Int,
    traceArray: IntArray,
    nodeTraceArray: IntArray,
    methodNodes: (Int) -> IntOpenHashSet?,
    nodeSuccessors: (Int) -> IntOpenHashSet?,
    next: () -> NodeTrace?
): NodeTrace? {
    if (i == traceArray.size) {
        return next()
    }

    val prevNode = nodeTraceArray[i - 1]
    val curMethodId = traceArray[i]

    val curCandidateNodes = methodNodes(curMethodId)
        ?: return null

    val successorNodes = nodeSuccessors(prevNode)
        ?: return null

    successorNodes.forEachInt { succNode ->
        if (!curCandidateNodes.contains(succNode)) return@forEachInt

        nodeTraceArray[i] = succNode

        processMethodTrace(i + 1, traceArray, nodeTraceArray, methodNodes, nodeSuccessors, next)
            ?.let { return it }
    }
    return null
}

enum class TracePathNodeKind {
    SOURCE, SINK, CALL, RETURN, OTHER
}

data class TracePathNode(val statement: CommonInst, val kind: TracePathNodeKind, val entry: TraceEntry?)

private fun generateSourceToSinkPath(
    trace: SourceToSinkTrace,
    pathNodes: ResolvedNodeTrace
): List<TracePathNode>? {
    val callToSourceTrace = resolveStartToSource(pathNodes.root2Source)

    val startTraceNode = callToSourceTrace.firstOrNull()
        ?: return null

    val startTraceStatement = startTraceNode.trace.lastOrNull()?.statement
        ?: return null

    val callToSinkTrace = resolveStartToSink(pathNodes.root2SinkNoRoot, startTraceStatement)

    val path = mutableListOf<TracePathNode>()

    var sourceNodeGenerated = false
    val callToSourceNoStart = callToSourceTrace.drop(1)

    for (call in callToSourceNoStart) {
        path += TracePathNode(call.callStatement, TracePathNodeKind.CALL, entry = null)
    }

    for (call in callToSourceNoStart.asReversed()) {
        var callPath = call.trace
        if (!sourceNodeGenerated) {
            val sourceNode = callPath.firstOrNull()
            if (sourceNode == null) {
                path.removeLast()
                continue
            }

            sourceNodeGenerated = true
            path += TracePathNode(sourceNode.statement, TracePathNodeKind.SOURCE, sourceNode)
            callPath = callPath.drop(1)
        }

        path += resolveCallPath(trace, call.node, callPath)

        path += TracePathNode(call.callStatement, TracePathNodeKind.RETURN, entry = null)
    }

    for ((idx, call) in callToSinkTrace.withIndex()) {
        var callPath = call.trace
        if (!sourceNodeGenerated) {
            val sourceNode = callPath.firstOrNull() ?: return null

            sourceNodeGenerated = true
            path += TracePathNode(sourceNode.statement, TracePathNodeKind.SOURCE, sourceNode)
            callPath = callPath.drop(1)
        }

        path += resolveCallPath(trace, call.node, callPath)

        if (idx == callToSinkTrace.lastIndex) {
            val sinkNode = callPath.lastOrNull() ?: return null

            path.removeLast()
            path += TracePathNode(sinkNode.statement, TracePathNodeKind.SINK, sinkNode)
        }
    }

    return path
}

private fun resolveCallPath(
    trace: SourceToSinkTrace,
    traceNode: InterProceduralTraceNode,
    callPath: List<TraceEntry>,
    stack: HashSet<CommonInst> = hashSetOf(),
): List<TracePathNode> {
    val path = mutableListOf<TracePathNode>()
    for (node in callPath) {
        var pathGenerated = false
        if (node.statement !in stack) {
            val innerTraces = trace.findInnerCallEntries(traceNode, node)
            if (innerTraces != null) {
                val innerTrace = innerTraces.map { it.node }
                    .filterIsInstance<InterProceduralFullTraceNode>()
                    .firstOrNull()

                if (innerTrace != null) {
                    path += TracePathNode(node.statement, TracePathNodeKind.CALL, node)
                    val innerPath = generateIntraProceduralPath(innerTrace.trace).orEmpty()
                    val newStack = HashSet<CommonInst>(stack)
                    newStack.add(node.statement)
                    path += resolveCallPath(trace, innerTrace, innerPath, newStack)
                    path += TracePathNode(node.statement, TracePathNodeKind.RETURN, node)
                    pathGenerated = true
                }
            }
        }

        if (!pathGenerated) {
            path += TracePathNode(node.statement, TracePathNodeKind.OTHER, node)
        }
    }
    return path
}

private fun SourceToSinkTrace.findInnerCallEntries(
    traceNode: InterProceduralTraceNode,
    node: TraceEntry
): List<TraceResolver.InterProceduralCall>? {
    if (node !is TraceEntry.Action) return null

    val action = node.primaryAction
    if (action !is TraceEntryAction.CallSummary) return null

    return findSuccessors(traceNode, CallInnerTrace, node.statement, action.summaryTrace)
}

data class CallTrace(
    val callStatement: CommonInst,
    val trace: List<TraceEntry>,
    val node: InterProceduralTraceNode,
)

private fun resolveStartToSource(
    nodes: List<InterProceduralTraceNode>,
): List<CallTrace> {
    val result = mutableListOf<CallTrace>()

    var statement: CommonInst = nodes.first().methodEntryPoint.statement
    for (node in nodes) {
        when (node) {
            is InterProceduralFullTraceNode -> {
                val path = generateIntraProceduralPath(node.trace) ?: return result
                result += CallTrace(statement, path, node)
                statement = node.trace.startEntry.statement
            }

            is TraceResolver.InterProceduralSummaryTraceNode -> {
                TODO("Start-2-source node is not full")
            }
        }
    }
    return result
}

private fun resolveStartToSink(
    nodes: List<InterProceduralTraceNode>,
    startStatement: CommonInst,
): List<CallTrace> {
    val result = mutableListOf<CallTrace>()

    var prevStatement = startStatement
    for (node in nodes) {
        val path = when (node) {
            is InterProceduralFullTraceNode -> {
                generateIntraProceduralPath(node.trace) ?: return result
            }

            is TraceResolver.InterProceduralSummaryTraceNode -> {
                listOf(node.trace.final)
            }
        }

        result += CallTrace(prevStatement, path, node)
        prevStatement = path.last().statement
    }

    return result
}

private fun generateIntraProceduralPath(
    trace: MethodTraceResolver.FullTrace
): PersistentList<TraceEntry>? {
    val unprocessed = ArrayDeque<Pair<TraceEntry, PersistentList<TraceEntry>>>()
    unprocessed.addFirst(trace.startEntry to persistentListOf<TraceEntry>(trace.startEntry))
    val visited = hashSetOf<TraceEntry>()

    while (unprocessed.isNotEmpty()) {
        val (entry, path) = unprocessed.removeFirst()

        if (entry == trace.final) {
            return path
        }

        if (!visited.add(entry)) continue

        trace.successors[entry]?.forEach {
            unprocessed.addLast(it to path.add(it))
        }
    }

    return null
}
