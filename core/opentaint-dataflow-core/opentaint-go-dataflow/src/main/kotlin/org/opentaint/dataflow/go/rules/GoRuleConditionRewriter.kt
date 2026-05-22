package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.ContainsMarkLiteral

class GoRuleConditionRewriter : RuleConditionRewriter<GoRuleCondition> {
    override fun rewriteAtom(
        atom: GoRuleCondition,
        negated: Boolean
    ): ExprOrConstant {
        when(atom) {
            is GoRuleCondition.ContainsMark ->  {
                val position = GoFlowFunctionUtils.resolvePositionAccess(atom.position)
                return ExprOrConstant(ContainsMarkLiteral(position, TaintMarkAccessor(atom.mark), negated))
            }
        }
    }
}
