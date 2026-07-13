package org.opentaint.common.sast.sarif

import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTrace
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTraceEntry
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedNodeTrace
import org.opentaint.dataflow.ap.ifds.trace.path.TracePathGenerationResult
import org.opentaint.ir.api.common.cfg.CommonInst

fun generateTracePath(trace: TracePathGenerationResult.Path, limit: Int?): List<List<TracePathNode>> {
    return trace.path.take(limit ?: Int.MAX_VALUE).map { generateSourceToSinkPath(it) }
}

enum class TracePathNodeKind {
    SOURCE, SINK, CALL, RETURN, OTHER
}

data class TracePathNode(val statement: CommonInst, val kind: TracePathNodeKind, val entry: TraceEntry?)

private fun generateSourceToSinkPath(
    trace: ResolvedNodeTrace,
): List<TracePathNode> {
    val callToSourceTrace = resolveStartToSource(trace.root2Source)

    val startTraceNode = callToSourceTrace.first()
    val startTraceStatement = startTraceNode.trace.last().entry.statement
    val callToSinkTrace = resolveStartToSink(
        listOf(trace.root2Source.first()) + trace.root2SinkNoRoot,
        startTraceStatement
    )

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
            path += TracePathNode(sourceNode.entry.statement, TracePathNodeKind.SOURCE, sourceNode.entry)
            callPath = callPath.drop(1)
        }

        path += resolveCallPath(callPath)

        path += TracePathNode(call.callStatement, TracePathNodeKind.RETURN, entry = null)
    }

    for ((idx, call) in callToSinkTrace.withIndex()) {
        var callPath = call.trace
        if (!sourceNodeGenerated) {
            val sourceNode = callPath.first()

            sourceNodeGenerated = true
            path += TracePathNode(sourceNode.entry.statement, TracePathNodeKind.SOURCE, sourceNode.entry)
            callPath = callPath.drop(1)
        }

        path += resolveCallPath(callPath)

        if (idx == callToSinkTrace.lastIndex) {
            val sinkNode = callPath.last()
            path.removeLast()
            path += TracePathNode(sinkNode.entry.statement, TracePathNodeKind.SINK, sinkNode.entry)
        }
    }

    return path
}

private fun resolveCallPath(
    callPath: List<ResolvedInterProceduralTraceEntry>
): List<TracePathNode> {
    val path = mutableListOf<TracePathNode>()
    for (node in callPath) {
        val entry = node.entry
        when (node) {
            is ResolvedInterProceduralTraceEntry.InnerCall -> {
                path += TracePathNode(entry.statement, TracePathNodeKind.CALL, entry)
                path += resolveCallPath(node.innerTrace.entries)
                path += TracePathNode(entry.statement, TracePathNodeKind.RETURN, entry)
            }
            is ResolvedInterProceduralTraceEntry.Simple -> {
                path += TracePathNode(entry.statement, TracePathNodeKind.OTHER, entry)
            }
        }
    }
    return path
}

data class CallTrace(
    val callStatement: CommonInst,
    val trace: List<ResolvedInterProceduralTraceEntry>,
    val node: ResolvedInterProceduralTrace,
)

private fun resolveStartToSource(
    nodes: List<ResolvedInterProceduralTrace>,
): List<CallTrace> {
    val result = mutableListOf<CallTrace>()

    var statement: CommonInst = nodes.first().method.statement
    for (node in nodes) {
        result += CallTrace(statement, node.entries, node)
        statement = node.entries.first().entry.statement
    }
    return result
}

private fun resolveStartToSink(
    nodes: List<ResolvedInterProceduralTrace>,
    startStatement: CommonInst,
): List<CallTrace> {
    val result = mutableListOf<CallTrace>()

    var prevStatement = startStatement
    for (node in nodes) {
        result += CallTrace(prevStatement, node.entries, node)
        prevStatement = node.entries.last().entry.statement
    }

    return result
}
