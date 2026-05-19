package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodStartPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition

/**
 * Go has no entry-point source rules in the current MVP rule model
 * (cf. [org.opentaint.dataflow.go.analysis.GoMethodStartFlowFunction.propagateZero]),
 * so no fact can be produced by a method-start source rule.
 */
class GoMethodStartPrecondition : MethodStartPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<TaintRulePrecondition.Source> = emptyList()
}
