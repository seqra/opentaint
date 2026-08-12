package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.SideEffectSummary
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.taint.MethodSideEffectHandlerWithAnyAccessorRequestHandling
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRMethodSideEffectHandler(
    private val statement: JIRInst,
    override val runner: AnalysisRunner
) : MethodSideEffectHandlerWithAnyAccessorRequestHandling {
    override fun prepareSideEffectSummary(
        sideEffectSummary: SideEffectSummary.FactSideEffectSummary,
    ): List<SideEffectSummary.FactSideEffectSummary> =
        JIRMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, sideEffectSummary.initialFactAp)
            .map { sideEffectSummary.copy(initialFactAp = it) }
}
