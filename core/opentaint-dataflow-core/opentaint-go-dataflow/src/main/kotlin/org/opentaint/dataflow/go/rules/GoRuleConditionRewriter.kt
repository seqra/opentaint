package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils.resolvePosAccess
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.falseExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.trueExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.ContainsMarkLiteral
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

class GoRuleConditionRewriter(
    callExpr: GoCallExpr,
    statement: GoIRInst,
    returnValue: GoIRValue?,
) : RuleConditionRewriter<GoRuleCondition> {
    private val positiveAtomEvaluator = GoBasicAtomEvaluator(negated = false, callExpr, statement, returnValue)
    private val negativeAtomEvaluator = GoBasicAtomEvaluator(negated = true, callExpr, statement, returnValue)

    override fun rewriteAtom(atom: GoRuleCondition, negated: Boolean): ExprOrConstant {
        if (!negated) {
            return rewriteAtom(atom, positiveAtomEvaluator)
        }
        return rewriteAtom(atom, negativeAtomEvaluator).negate()
    }

    private fun rewriteAtom(atom: GoRuleCondition, evaluator: GoBasicAtomEvaluator): ExprOrConstant {
        if (atom is GoRuleCondition.ContainsMark) {
            val pos = atom.position.resolvePosAccess()
            val literal = ContainsMarkLiteral(pos, TaintMarkAccessor(atom.mark), negated = false)
            return ExprOrConstant(literal)
        }

        if (atom is GoRuleCondition.ContainsMarkOnAnyAccessor) {
            val pos = atom.position.resolvePosAccess()
            val literal = ContainsMarkOnAnyAccessorLiteral(pos, TaintMarkAccessor(atom.mark), negated = false)
            return ExprOrConstant(literal)
        }

        val result = atom.accept(evaluator)
        return if (result) trueExpr else falseExpr
    }
}
