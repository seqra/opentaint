package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallSummaryHandler
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRBackwardMethodCallSummaryHandler(
    private val statement: JIRInst,
    analysisContext: JIRMethodAnalysisContext,
    apManager: ApManager,
) : JIRMethodCallSummaryHandler(statement, analysisContext, apManager) {
    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> =
        JIRBackwardMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact, factTypeChecker)

    override fun applyCallAliases(fact: FinalFactAp, body: (FinalFactAp) -> Unit) {}

    override fun prepareFactToFactSummary(summaryEdge: Edge.FactToFact): List<Edge.FactToFact> = listOf(summaryEdge)

    override fun prepareNDFactToFactSummary(summaryEdge: Edge.NDFactToFact): List<Edge.NDFactToFact> = listOf(summaryEdge)
}
