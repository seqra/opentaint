package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.trace.MethodTraceResolver.TraceEntryAction

interface InnerCallTraceResolveStrategy {
    fun innerCallTraceIsRelevant(callSummary: TraceEntryAction.CallSummary): Boolean =
        callSummary.summaryEdges.any { innerCallSummaryEdgeIsRelevant(it) }

    fun innerCallSummaryEdgeIsRelevant(summaryEdge: TraceEntryAction.TraceSummaryEdge): Boolean =
        when (summaryEdge) {
            is TraceEntryAction.TraceSummaryEdge.SourceSummary -> true
            is TraceEntryAction.TraceSummaryEdge.MethodSummary -> summaryEdge.edge.fact != summaryEdge.edgeAfter.fact
        }

    object Default : InnerCallTraceResolveStrategy
}
