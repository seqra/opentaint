package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact.CallFailurePreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.PassRuleConditionFacts
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodStartPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition

object JIRBackwardMethodStartPrecondition : MethodStartPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<TaintRulePrecondition.Source> = emptyList()
}

object JIRBackwardMethodSequentPrecondition : MethodSequentPrecondition {
    override fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition> =
        setOf(SequentPrecondition.Unchanged)
}

object JIRBackwardMethodCallPrecondition : MethodCallPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<CallPrecondition> =
        listOf(CallPrecondition.Unchanged)

    override fun factPreconditionResolutionFailure(
        fact: InitialFactAp,
        startFactBase: AccessPathBase
    ): List<CallFailurePreconditionFact> = emptyList()

    override fun resolvePassRuleCondition(
        precondition: PassRuleCondition,
        edges: MethodAnalyzerEdges
    ): List<PassRuleConditionFacts> = emptyList()
}
