package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.SideEffectSummary
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.taint.MethodSideEffectHandlerWithAnyAccessorRequestHandling
import org.opentaint.ir.go.inst.GoIRInst

class GoMethodSideEffectHandler(
    private val statement: GoIRInst,
    override val runner: AnalysisRunner
) : MethodSideEffectHandlerWithAnyAccessorRequestHandling {
    override fun prepareSideEffectSummary(
        sideEffectSummary: SideEffectSummary.FactSideEffectSummary,
    ): List<SideEffectSummary.FactSideEffectSummary> =
        GoMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, sideEffectSummary.initialFactAp)
            .map { sideEffectSummary.copy(initialFactAp = it) }
}
