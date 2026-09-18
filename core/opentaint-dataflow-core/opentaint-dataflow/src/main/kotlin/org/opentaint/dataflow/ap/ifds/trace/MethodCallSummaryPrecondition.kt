package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

interface MethodCallSummaryPrecondition {
    fun callSummaryPrecondition(fact: InitialFactAp, callee: MethodEntryPoint): List<InitialFactAp>
}
