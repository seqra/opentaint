package org.opentaint.dataflow.ap.ifds.trace.path

import it.unimi.dsi.fastutil.ints.IntObjectImmutablePair
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.trace.InnerCallTraceResolveStrategy
import org.opentaint.dataflow.ap.ifds.trace.InnerCallTraceResolveStrategy.Default
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.ActionVariant
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver.SourceToSinkTrace
import org.opentaint.dataflow.ap.ifds.trace.withMethodRunner
import org.opentaint.dataflow.util.forEachInt

private val logger = object : KLogging() {}.logger

sealed interface TracePathGenerationResult {
    data class Path(val path: List<ResolvedNodeTrace>) : TracePathGenerationResult
    data object Simple : TracePathGenerationResult
    data object Failure : TracePathGenerationResult
}

data class TracePathResolveParams(
    val limit: Int? = null,
    val sourceToSinkInnerTraceResolutionLimit: Int? = null,
    val innerCallTraceResolveStrategy: InnerCallTraceResolveStrategy = Default,
)

fun TaintAnalysisUnitRunnerManager.generateTracePath(
    trace: TraceResolver.Trace?,
    params: TracePathResolveParams
): TracePathGenerationResult {
    if (trace == null) return TracePathGenerationResult.Failure

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

        val nodeTraces = enumerateTraces(sourceToSinkTrace, this, params)
        if (nodeTraces.isEmpty()) {
            logger.error { "Trace has no resolved paths" }
            return TracePathGenerationResult.Failure
        }

        return TracePathGenerationResult.Path(nodeTraces)
    } catch (ex: Throwable) {
        logger.error(ex) { "Failed to generate trace path" }
        return TracePathGenerationResult.Failure
    }
}

private class NodeTrace(val sink2Root: IntArray, val root2Source: IntArray)

sealed interface ResolvedInterProceduralTraceEntry {
    val entry: TraceEntry

    data class Simple(
        override val entry: TraceEntry,
    ) : ResolvedInterProceduralTraceEntry

    data class Action(
        override val entry: TraceEntry.Action,
        val actionVariant: ActionVariant,
    ): ResolvedInterProceduralTraceEntry

    data class InnerCall(
        override val entry: TraceEntry.Action,
        val actionVariant: ActionVariant,
        val innerTrace: ResolvedInterProceduralTrace,
    ) : ResolvedInterProceduralTraceEntry
}

class ResolvedInterProceduralTrace(
    val method: MethodEntryPoint,
    val entries: List<ResolvedInterProceduralTraceEntry>
)

class ResolvedNodeTrace(
    val root2Source: List<ResolvedInterProceduralTrace>,
    val root2SinkNoRoot: List<ResolvedInterProceduralTrace>,
)

private fun enumerateTraces(
    trace: SourceToSinkTrace,
    runner: TaintAnalysisUnitRunnerManager,
    params: TracePathResolveParams,
): List<ResolvedNodeTrace> {
    val graph = createSource2SinkGraph(trace)

    val methodGraph = graph.methodGraph()
    val nodeTraces = methodGraph.allMethodTraces(params.limit) {
        graph.processMethodTrace(methodGraph, it) { nodeTrace ->
            graph.resolvedNodeTrace(nodeTrace, runner, params)
        }
    }

    return nodeTraces
}

private fun Source2SinkTraceGraph.resolvedNodeTrace(
    trace: NodeTrace,
    runner: TaintAnalysisUnitRunnerManager,
    params: TracePathResolveParams,
): ResolvedNodeTrace? {
    val root2Source = trace.root2Source.map { allNodes[it] }
    val root2Sink = trace.sink2Root.map { allNodes[it] }.reversed()

    val resolvedRoot2Source = root2Source.map {
        runner.resolveNodePath(it, params) ?: return null
    }

    val rootToSinkNoRoot = root2Sink.drop(1).map {
        runner.resolveNodePath(it, params) ?: return null
    }

    return ResolvedNodeTrace(resolvedRoot2Source, rootToSinkNoRoot)
}

private fun <T> Source2SinkTraceGraph.processMethodTrace(
    mg: Source2SinkMethodTraceGraph,
    trace: MethodTrace,
    handleNodeTrace: (NodeTrace) -> T?
): T? {
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
        }?.let {
            handleNodeTrace(it)?.let { return it }
        }
    }
    return null
}

private fun <T> processMethodTrace(
    i: Int,
    traceArray: IntArray,
    nodeTraceArray: IntArray,
    methodNodes: (Int) -> IntOpenHashSet?,
    nodeSuccessors: (Int) -> IntOpenHashSet?,
    next: () -> T?
): T? {
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

private fun TaintAnalysisUnitRunnerManager.resolveNodePath(
    node: TraceResolver.InterProceduralTraceNode,
    params: TracePathResolveParams,
): ResolvedInterProceduralTrace? {
    val traces = withMethodRunner(node.methodEntryPoint) {
        val traceResolver = methodTraceResolver(node.methodEntryPoint)
        when (node) {
            is TraceResolver.InterProceduralStart2FinalTraceNode -> {
                traceResolver.resolveIntraProceduralFullStart2FinalTrace(
                    node.trace, cancellation, collapseUnchangedNodes = true
                )
            }

            is TraceResolver.InterProceduralSummaryTraceNode -> {
                traceResolver.resolveIntraProceduralFullStart2FinalTrace(
                    node.trace, cancellation, collapseUnchangedNodes = true
                )
            }
        }
    }

    for (trace in traces) {
        resolveInterProceduralTracePath(trace, params, depth = 0)?.let { return it }
    }

    return null
}

private fun TaintAnalysisUnitRunnerManager.resolveInterProceduralTracePath(
    trace: MethodTraceResolver.FullStart2FinalTrace,
    params: TracePathResolveParams,
    depth: Int,
): ResolvedInterProceduralTrace? {
    val unprocessed = ArrayDeque<IntObjectImmutablePair<IntArray>>()
    unprocessed.addFirst(IntObjectImmutablePair(trace.startEntryId, intArrayOf(trace.startEntryId)))
    val visited = IntOpenHashSet()

    while (unprocessed.isNotEmpty()) {
        val state = unprocessed.removeFirst()
        val entry = state.leftInt()
        val path = state.right()

        if (entry == trace.finalId) {
            val resolved = resolveEntries(trace, path, params, depth)
            if (resolved != null) {
                return ResolvedInterProceduralTrace(trace.method, resolved)
            }
        }

        if (!visited.add(entry)) continue

        trace.successors[entry]?.forEach {
            val updatedPath = path.plus(it)
            unprocessed.addLast(IntObjectImmutablePair(it, updatedPath))
        }
    }

    return null
}

private fun TaintAnalysisUnitRunnerManager.resolveEntries(
    trace: MethodTraceResolver.FullStart2FinalTrace,
    entryIds: IntArray,
    params: TracePathResolveParams,
    depth: Int,
): List<ResolvedInterProceduralTraceEntry>? =
    entryIds.map { entryId ->
        resolveEntry(trace, trace.entries[entryId], entryId, params, depth) ?: return null
    }

private fun TaintAnalysisUnitRunnerManager.resolveEntry(
    trace: MethodTraceResolver.FullStart2FinalTrace,
    entry: TraceEntry,
    entryId: Int,
    params: TracePathResolveParams,
    depth: Int,
): ResolvedInterProceduralTraceEntry? {
    if (params.sourceToSinkInnerTraceResolutionLimit != null) {
        if (depth > params.sourceToSinkInnerTraceResolutionLimit) {
            return ResolvedInterProceduralTraceEntry.Simple(entry)
        }
    }

    if (entry !is TraceEntry.Action) {
        return ResolvedInterProceduralTraceEntry.Simple(entry)
    }

    val variants = trace.actionVariants.get(entryId)
    for (variant in variants) {
        resolveActionVariant(entry, variant, params, depth)?.let { return it }
    }
    return null
}

private fun TaintAnalysisUnitRunnerManager.resolveActionVariant(
    entry: TraceEntry.Action,
    variant: ActionVariant,
    params: TracePathResolveParams,
    depth: Int,
): ResolvedInterProceduralTraceEntry? {
    val action = variant.primaryAction
    if (action !is TraceEntryAction.CallSummary) {
        return ResolvedInterProceduralTraceEntry.Action(entry, variant)
    }
    if (!params.innerCallTraceResolveStrategy.innerCallTraceIsRelevant(action)) {
        return ResolvedInterProceduralTraceEntry.Action(entry, variant)
    }

    val summary = action.summaryTrace
    val innerTraces = withMethodRunner(summary.method) {
        val traceResolver = methodTraceResolver(summary.method)
        traceResolver.resolveIntraProceduralFullStart2FinalTrace(
            summary, cancellation, collapseUnchangedNodes = true
        )
    }

    for (trace in innerTraces) {
        resolveInterProceduralTracePath(trace, params, depth + 1)?.let {
            return ResolvedInterProceduralTraceEntry.InnerCall(entry, variant, it)
        }
    }

    return null
}
