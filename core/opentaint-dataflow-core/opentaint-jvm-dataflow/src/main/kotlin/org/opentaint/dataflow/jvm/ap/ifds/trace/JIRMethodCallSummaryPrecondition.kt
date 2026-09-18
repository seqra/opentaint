package org.opentaint.dataflow.jvm.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodCallSummaryPrecondition
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRMethodCallSummaryPrecondition(
    private val statement: JIRInst,
) : MethodCallSummaryPrecondition {
    override fun callSummaryPrecondition(fact: InitialFactAp, callee: MethodEntryPoint): List<InitialFactAp> =
        JIRMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact)
}
