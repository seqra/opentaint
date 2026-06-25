package org.opentaint.dataflow.python

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.python.AnyArgument
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.PythonRuleCondition
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.falseExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.Companion.trueExpr
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.ContainsMarkLiteral
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArgKind

/**
 * Rewrites a compiled [PythonRuleCondition] against the concrete [call] it is checked at.
 * `ContainsMark` becomes a taint-fact literal; an `arg(*)` ([AnyArgument]) `ContainsMark` is
 * unpacked here into an OR over the call's positional arguments (the signature can't be trusted
 * for Python varargs). Every other (basic) atom is decided to a constant true/false by
 * [PIRBasicAtomEvaluator]. Mirrors `GoRuleConditionRewriter`.
 */
class PIRConditionRewriter(private val call: PIRCall) : RuleConditionRewriter<PythonRuleCondition> {
    private val atomEvaluator = PIRBasicAtomEvaluator(call)

    override fun rewriteAtom(atom: PythonRuleCondition, negated: Boolean): ExprOrConstant {
        if (!negated) {
            return rewriteAtom(atom)
        }
        return rewriteAtom(atom).negate()
    }

    private fun rewriteAtom(atom: PythonRuleCondition): ExprOrConstant {
        if (atom is ContainsMark) {
            if (atom.pos.rootBase() is AnyArgument) return expandAnyArgument(atom)

            val pos = atom.pos.resolveAp() ?: return falseExpr
            val literal = ContainsMarkLiteral(pos, TaintMarkAccessor(atom.mark.name), negated = false)
            return ExprOrConstant(literal)
        }

        val result = atom.accept(atomEvaluator)
        return if (result) trueExpr else falseExpr
    }

    /** `ContainsMark` over `arg(*)` = mark on some positional argument of the concrete call. */
    private fun expandAnyArgument(atom: ContainsMark): ExprOrConstant {
        val perArg = call.args.indices
            .filter { call.args[it].kind == PIRCallArgKind.POSITIONAL }
            .map { CommonCondition.Atom<PythonRuleCondition>(ContainsMark(atom.mark, atom.pos.replaceRoot(Argument(it)))) }
        return rewriteOrCondition(perArg)
    }

    private fun Position.rootBase(): Position = when (this) {
        is PositionWithAccess -> base.rootBase()
        else -> this
    }

    private fun Position.replaceRoot(newRoot: Position): Position = when (this) {
        is PositionWithAccess -> PositionWithAccess(base.replaceRoot(newRoot), access)
        else -> newRoot
    }
}
