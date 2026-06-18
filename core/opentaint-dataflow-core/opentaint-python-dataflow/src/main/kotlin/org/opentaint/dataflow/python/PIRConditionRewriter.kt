package org.opentaint.dataflow.python

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.PythonRuleCondition
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.falseExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.trueExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.ContainsMarkLiteral
import org.opentaint.ir.api.python.PIRCall

/**
 * Rewrites a compiled [PythonRuleCondition] against the concrete [call] it is checked at.
 * `ContainsMark` becomes a taint-fact literal; every other (basic) atom is decided to a
 * constant true/false by [PIRBasicAtomEvaluator]. Mirrors `GoRuleConditionRewriter`.
 */
class PIRConditionRewriter(call: PIRCall) : RuleConditionRewriter<PythonRuleCondition> {
    private val atomEvaluator = PIRBasicAtomEvaluator(call)

    override fun rewriteAtom(atom: PythonRuleCondition, negated: Boolean): ExprOrConstant {
        if (!negated) {
            return rewriteAtom(atom)
        }
        return rewriteAtom(atom).negate()
    }

    private fun rewriteAtom(atom: PythonRuleCondition): ExprOrConstant {
        if (atom is ContainsMark) {
            val pos = atom.pos.resolveAp() ?: return falseExpr
            val literal = ContainsMarkLiteral(pos, TaintMarkAccessor(atom.mark.name), negated = false)
            return ExprOrConstant(literal)
        }

        val result = atom.accept(atomEvaluator)
        return if (result) trueExpr else falseExpr
    }
}
