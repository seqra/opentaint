package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.SideEffectSummary
import org.opentaint.dataflow.taint.MethodSideEffectHandlerWithAnyAccessorRequestHandling
import org.opentaint.ir.api.python.PIRCall

class PIRMethodSideEffectSummaryHandler(
    private val callInst: PIRCall,
    private val ctx: PIRMethodAnalysisContext,
    override val runner: AnalysisRunner,
) : MethodSideEffectHandlerWithAnyAccessorRequestHandling {
    override fun prepareSideEffectSummary(
        sideEffectSummary: SideEffectSummary.FactSideEffectSummary,
    ): List<SideEffectSummary.FactSideEffectSummary> =
        ctx.methodCallFactMapper.mapMethodExitToReturnFlowFact(callInst, sideEffectSummary.initialFactAp)
            .map { sideEffectSummary.copy(initialFactAp = it) }
}
