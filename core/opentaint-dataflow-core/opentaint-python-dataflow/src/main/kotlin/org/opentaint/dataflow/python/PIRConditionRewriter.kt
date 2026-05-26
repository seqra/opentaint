package org.opentaint.dataflow.python

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.falseExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.trueExpr
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr

object PIRConditionRewriter : RuleConditionRewriter<ContainsMark> {
    override fun rewriteAtom(
        atom: ContainsMark,
        negated: Boolean
    ): RuleConditionRewriter.ExprOrConstant {
        val pos = atom.pos.resolveAp()

        if (pos == null) {
            return if (!negated) {
                falseExpr
            } else {
                trueExpr
            }
        }

        val taintMark = TaintMarkAccessor(atom.mark.name)
        val expr = TaintMarkAwareConditionExpr.ContainsMarkLiteral(pos, taintMark, negated)
        return RuleConditionRewriter.ExprOrConstant(expr)
    }
}
