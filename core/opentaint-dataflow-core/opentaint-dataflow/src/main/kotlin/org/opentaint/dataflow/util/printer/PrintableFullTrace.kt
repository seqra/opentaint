package org.opentaint.dataflow.util.printer

import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.FullStart2FinalTrace
import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntry

fun FullStart2FinalTrace.view() {
    PrintableFullTrace(this).view(name = "")
}

private class PrintableFullTrace(
    private val trace: FullStart2FinalTrace,
) : PrintableGraph<Int, Pair<Int, Int>> {
    override fun allNodes(): List<Int> {
        val result = mutableSetOf(trace.startEntryId, trace.finalId)
        result.addAll(trace.successors.keys)
        trace.successors.values.forEach { set ->
            set.forEach { result.add(it) }
        }
        return result.toList()
    }

    override fun edgeLabel(edge: Pair<Int, Int>): String = ""

    override fun successors(node: Int): List<Pair<Pair<Int, Int>, Int>> =
        trace.successors.get(node)?.toSet().orEmpty().map { (node to it) to it }

    override fun nodeLabel(node: Int): String = nodeLabel(trace.entries[node])

    fun nodeLabel(node: TraceEntry): String = when (node) {
        is TraceEntry.Action -> "Action{${node.statement}}(${node.nodeEdgesStr()})[${node.actionStr()}]"
        is TraceEntry.Final -> "Final{${node.statement}}(${node.nodeEdgesStr()})"
        is TraceEntry.MethodEntry -> "Entry{${node.statement}}(${node.nodeEdgesStr()})"
        is TraceEntry.SourceStartEntry -> "SourceStart{${node.statement}}(${node.nodeEdgesStr()})"
        is TraceEntry.Unchanged -> "Unchanged{${node.statement}}(${node.nodeEdgesStr()})"
    }

    private fun TraceEntry.nodeEdgesStr(): String {
        val facts = edges.map { it.fact }.map { it.toString() }
        if (facts.size == 1) return facts.first()
        return facts.joinToString("\n")
    }

    private fun TraceEntry.Action.actionStr(): String {
        return this.toString()
    }
}
