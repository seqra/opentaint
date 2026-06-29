package org.opentaint.dataflow.python

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.configuration.python.AnyArgument
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.NumberOfArgs
import org.opentaint.dataflow.configuration.python.TaintMark
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.RuleConditionRewriter.ExprOrConstant
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.ContainsMarkLiteral
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr.Or
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRCallArg
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRLocation
import org.opentaint.ir.api.python.PIRStrConst
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Arity (`NumberOfArgs`) and `arg(*)` (`AnyArgument`) `ContainsMark` are decided against the
 * concrete call, not the signature — Python keeps the `*args` spread at the call site. These
 * tests pin that call-site behaviour directly.
 */
class PIRCallSiteConditionTest {

    @Test
    fun `arity matches the exact positional count`() {
        val e = PIRBasicAtomEvaluator(call(pos(), pos()))
        assertTrue(e.visit(NumberOfArgs(2)))
        assertFalse(e.visit(NumberOfArgs(1)))
        assertFalse(e.visit(NumberOfArgs(3)))
    }

    @Test
    fun `keyword args do not count toward positional arity`() {
        val e = PIRBasicAtomEvaluator(call(pos(), kw("b")))
        assertTrue(e.visit(NumberOfArgs(1)))
        assertFalse(e.visit(NumberOfArgs(2)))
    }

    @Test
    fun `a star spread removes the arity upper bound`() {
        val e = PIRBasicAtomEvaluator(call(pos(), star()))
        assertTrue(e.visit(NumberOfArgs(1)), "the concrete positional arg is the lower bound")
        assertTrue(e.visit(NumberOfArgs(50)), "the spread can supply any number of further args")
        assertFalse(e.visit(NumberOfArgs(0)), "below the concrete positional count is infeasible")
    }

    @Test
    fun `arg star ContainsMark expands over positional args only`() {
        val idxs = argumentIndicesOf(rewriteAnyArgMark(call(pos(), pos(), kw("b"))).expr as Or)
        assertEquals(listOf(0, 1), idxs, "the keyword arg is excluded from arg(*) expansion")
    }

    @Test
    fun `arg star ContainsMark with a single positional arg yields one literal`() {
        val r = rewriteAnyArgMark(call(pos()))
        assertFalse(r.isFalse)
        val lit = r.expr as ContainsMarkLiteral
        assertEquals(0, argumentIndexOf(lit))
    }

    @Test
    fun `arg star ContainsMark with no positional args is false`() {
        assertTrue(rewriteAnyArgMark(call(kw("b"))).isFalse)
    }

    private fun rewriteAnyArgMark(call: PIRCall): ExprOrConstant =
        PIRConditionRewriter(call).rewriteAtom(ContainsMark(TaintMark("t"), AnyArgument), negated = false)

    private fun argumentIndicesOf(or: Or): List<Int> = or.args.map { argumentIndexOf(it as ContainsMarkLiteral) }

    private fun argumentIndexOf(lit: ContainsMarkLiteral): Int =
        ((lit.position as PositionAccess.Simple).base as AccessPathBase.Argument).idx

    private fun call(vararg args: PIRCallArg): PIRCall =
        PIRCall(target = null, callee = PIRStrConst("callee"), args = args.toList(), location = unusedLocation)

    private fun pos(): PIRCallArg = PIRCallArg(PIRStrConst("x"), PIRCallArgKind.POSITIONAL)
    private fun kw(name: String): PIRCallArg = PIRCallArg(PIRStrConst("x"), PIRCallArgKind.KEYWORD, name)
    private fun star(): PIRCallArg = PIRCallArg(PIRStrConst("x"), PIRCallArgKind.STAR)

    private val unusedLocation = object : PIRLocation {
        override val method: PIRFunction get() = error("location is never read by the call-site evaluators")
        override val index: Int = 0
    }
}
