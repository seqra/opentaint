package org.opentaint.dataflow.python

import org.opentaint.dataflow.configuration.python.AnyArgument
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.BoolConstantValue
import org.opentaint.dataflow.configuration.python.ClassRef
import org.opentaint.dataflow.configuration.python.ConstantCmp
import org.opentaint.dataflow.configuration.python.ConstantCmpType
import org.opentaint.dataflow.configuration.python.ConstantMatches
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.IntConstantValue
import org.opentaint.dataflow.configuration.python.KwArgument
import org.opentaint.dataflow.configuration.python.NumberOfArgs
import org.opentaint.dataflow.configuration.python.PIRConditionVisitor
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.PositionWithAccess
import org.opentaint.dataflow.configuration.python.Result
import org.opentaint.dataflow.configuration.python.StrConstantValue
import org.opentaint.dataflow.configuration.python.This
import org.opentaint.ir.api.python.PIRBoolConst
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRIntConst
import org.opentaint.ir.api.python.PIRStrConst
import org.opentaint.ir.api.python.PIRValue

interface PIRBasicAtomEvaluator : PIRConditionVisitor<Boolean> {
    override fun visit(c: ContainsMark): Boolean =
        error("ContainsMark is a taint-fact atom; handle it in condition rewriter, not the evaluator")
}

/**
 * Evaluates the statically-decidable atoms of a [org.opentaint.dataflow.configuration.python.PythonRuleCondition]
 * against the concrete [call] — mirrors `GoBasicAtomEvaluator` / `JIRBasicAtomEvaluator`. The taint-fact atom
 * [ContainsMark] is not basic: it is handled by [PIRConditionRewriter], so visiting it here is a bug.
 */
class PIRCallAtomEvaluator(private val call: PIRCall) : PIRBasicAtomEvaluator {
    override fun visit(c: NumberOfArgs): Boolean {
        val positional = call.args.count { it.kind == PIRCallArgKind.POSITIONAL }
        val hasStar = call.args.any { it.kind == PIRCallArgKind.STAR }
        val max = if (hasStar) Int.MAX_VALUE else positional

        return c.n in positional..max
    }

    override fun visit(c: ConstantCmp): Boolean {
        val v = valueAt(c.pos) ?: return false
        return when (val expected = c.value) {
            is IntConstantValue -> v is PIRIntConst && when (c.cmp) {
                ConstantCmpType.Eq -> v.value == expected.value
                ConstantCmpType.Lt -> v.value < expected.value
                ConstantCmpType.Gt -> v.value > expected.value
            }
            is StrConstantValue -> v is PIRStrConst && when (c.cmp) {
                ConstantCmpType.Eq -> v.value == expected.value
                ConstantCmpType.Lt -> TODO()
                ConstantCmpType.Gt -> TODO()
            }
            is BoolConstantValue -> v is PIRBoolConst && when (c.cmp) {
                ConstantCmpType.Eq -> v.value == expected.value
                ConstantCmpType.Lt -> TODO()
                ConstantCmpType.Gt -> TODO()
            }
        }
    }

    override fun visit(c: ConstantMatches): Boolean {
        val v = valueAt(c.pos)
        return v is PIRStrConst && c.pattern.matches(v.value)
    }

    private fun valueAt(pos: Position): PIRValue? = when (pos) {
        is Argument -> call.args.getOrNull(pos.index)?.value
        is KwArgument -> call.args.firstOrNull { it.kind == PIRCallArgKind.KEYWORD && it.keyword == pos.name }?.value
        is Result -> call.target

        AnyArgument -> error("AnyArgument is only supported for ContainsMark")

        is ClassRef,
        is This,
        is PositionWithAccess -> null
    }
}

object PIRAttrLoadAtomEvaluator : PIRBasicAtomEvaluator {
    override fun visit(c: NumberOfArgs): Boolean {
        return c.n == 0
    }

    override fun visit(c: ConstantCmp): Boolean {
        error("Unexpected atom for attribute load rule: $c")
    }

    override fun visit(c: ConstantMatches): Boolean {
        error("Unexpected atom for attribute load rule: $c")
    }
}
