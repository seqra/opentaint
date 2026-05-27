package org.opentaint.dataflow.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr

sealed interface TaintRulePrecondition {
    sealed interface PassRuleCondition {
        data class Expr(val expr: TaintMarkAwareConditionExpr) : PassRuleCondition
        data class Fact(val fact: InitialFactAp) : PassRuleCondition
        data class FactWithExpr(val fact: InitialFactAp, val expr: TaintMarkAwareConditionExpr) : PassRuleCondition
    }

    data class Source(
        val rule: CommonTaintConfigurationSource,
        val action: Set<CommonTaintAssignAction>,
    ) : TaintRulePrecondition

    data class Pass(
        val rule: CommonTaintConfigurationItem,
        val action: Set<CommonTaintAction>,
        val condition: PassRuleCondition,
    ) : TaintRulePrecondition
}
