package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallSummaryHandler

class JIRBackwardMethodCallSummaryHandler(
    forward: JIRMethodCallSummaryHandler,
) : MethodCallSummaryHandler by forward {
    override fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> = listOf(summaryEdge)

    override fun prepareNDFactToFactSummary(summaryEdge: Edge.NDFactToFact): List<Edge.NDFactToFact> = listOf(summaryEdge)
}
