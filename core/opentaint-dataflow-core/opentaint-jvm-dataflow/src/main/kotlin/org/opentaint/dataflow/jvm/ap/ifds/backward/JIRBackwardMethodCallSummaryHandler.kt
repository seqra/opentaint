package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRBackwardMethodCallSummaryHandler(
    private val statement: JIRInst,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
) : MethodCallSummaryHandler {
    override val factTypeChecker: FactTypeChecker get() = analysisContext.factTypeChecker

    override fun mapMethodExitToReturnFlowFact(fact: FinalFactAp): List<FinalFactAp> =
        JIRBackwardMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact, factTypeChecker)
}
