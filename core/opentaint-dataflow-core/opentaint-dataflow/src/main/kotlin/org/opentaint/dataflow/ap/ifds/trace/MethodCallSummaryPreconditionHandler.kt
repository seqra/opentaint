package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.Edge

interface MethodCallSummaryPreconditionHandler {
    fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> = listOf(summaryEdge)
}
