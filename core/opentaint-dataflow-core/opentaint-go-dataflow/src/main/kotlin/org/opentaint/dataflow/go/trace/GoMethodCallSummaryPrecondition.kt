package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodCallSummaryPrecondition
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.ir.go.inst.GoIRInst

class GoMethodCallSummaryPrecondition(
    private val statement: GoIRInst,
) : MethodCallSummaryPrecondition {
    override fun callSummaryPrecondition(fact: InitialFactAp, callee: MethodEntryPoint): List<InitialFactAp> =
        GoMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact)
}
