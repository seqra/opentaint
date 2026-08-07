package org.opentaint.dataflow.jvm.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.PassRuleConditionFacts
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition

/**
 * Non-method call sites have no callee summaries or method rules to reconstruct.
 */
object JIRNonMethodCallPrecondition : MethodCallPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<CallPrecondition> =
        listOf(CallPrecondition.Unchanged)

    override fun factPreconditionResolutionFailure(
        fact: InitialFactAp,
        startFactBase: AccessPathBase,
    ): List<CallPreconditionFact.CallFailurePreconditionFact> =
        listOf(CallPreconditionFact.UnresolvedCallSkip)

    override fun resolvePassRuleCondition(
        precondition: PassRuleCondition,
        edges: MethodAnalyzerEdges,
    ): List<PassRuleConditionFacts> = emptyList()
}
