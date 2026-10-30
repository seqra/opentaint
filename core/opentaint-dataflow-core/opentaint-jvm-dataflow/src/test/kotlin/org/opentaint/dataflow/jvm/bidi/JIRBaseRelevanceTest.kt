package org.opentaint.dataflow.jvm.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.bidi.ap.Direction
import org.opentaint.dataflow.bidi.interp.CallStage
import org.opentaint.dataflow.bidi.interp.RuleView
import org.opentaint.dataflow.bidi.interp.StageKind
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.Result
import org.opentaint.dataflow.configuration.jvm.TaintMark
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.bidi.fixtures.CallRules
import org.opentaint.dataflow.jvm.bidi.fixtures.NoTaintRules
import org.opentaint.dataflow.jvm.bidi.interp.JIRInterpreter
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRField
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.jvm.graph.JMethodBoundaryInst
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/** Compiled forms are the observer/transfer oracle; relevance must include their external inputs. */
class JIRBaseRelevanceTest : BidiJIRTestUtils() {
    private val callOwner = "sample.bidi.BidiCallSample"
    private val unrelated = AccessPathBase.Argument(1234)

    private fun assertStatementInputs(owner: JIRInterpreter, method: JIRMethod, at: JIRInst) {
        val forms = owner.forms(key(method))
        for (view in RuleView.entries) for (direction in Direction.entries) {
            val compiled = forms.statement(direction, at, view)
            val inputs = compiled.touched + compiled.typeFilters.keys + compiled.resultFilters.keys
            for (base in inputs) assertTrue(forms.isBaseRelevant(direction, at, base, view),
                "$direction/$view omitted compiled statement input $base at $at")
            assertTrue(forms.isBaseRelevant(direction, at, AccessPathBase.Zero, view), "ZERO at $at")
        }
    }

    private fun assertCallInputs(owner: JIRInterpreter, method: JIRMethod, at: JIRInst) {
        val forms = owner.forms(key(method))
        for (view in RuleView.entries) for (direction in Direction.entries) {
            val plan = forms.call(direction, at, checkNotNull(at.callExpr), view)
            // Internal BOUND/REWRITTEN positions are not caller coordinates.
            // Generic reverse forms retain former internal touched bases too.
            // The outer call gate admits only plan.touched before selecting its entry stages.
            val inputs = plan.stages.filterIsInstance<CallStage.Edges>()
                .filter { it.from == plan.entry }
                .flatMap { it.summary.touched + it.summary.typeFilters.keys + it.summary.resultFilters.keys }
                .toSet().intersect(plan.touched)
            assertTrue(inputs.isNotEmpty(), "Expected a compiled external entry binding at $at")
            for (base in inputs + plan.touched) assertTrue(forms.isBaseRelevant(direction, at, base, view),
                "$direction/$view omitted compiled call-entry input $base at $at")
            assertTrue(forms.isBaseRelevant(direction, at, AccessPathBase.ClassStatic, view))
            assertTrue(forms.isBaseRelevant(direction, at, AccessPathBase.Zero, view))
            assertFalse(forms.isBaseRelevant(direction, at, unrelated, view))
        }
    }

    @Test fun `statement footprint includes compiled read write cast return and throw inputs in both views`(): Unit {
        var statements = 0
        for (name in listOf("copy", "fieldRead", "fieldWrite", "fieldToField", "staticRead", "staticWrite",
            "arrayRead", "arrayWrite", "cast", "binary", "selfRead", "selfWrite", "throwValue")) {
            val method = method(name)
            val forms = interp.forms(key(method))
            for (at in method.instList.instructions) {
                if (at.callExpr != null || at is JMethodBoundaryInst) continue
                assertStatementInputs(interp, method, at)
                for (view in RuleView.entries) for (direction in Direction.entries)
                    assertFalse(forms.isBaseRelevant(direction, at, unrelated, view), "Unrelated base at $at")
                statements++
            }
        }
        assertTrue(statements > 20)
    }

    @Test fun `call footprint uses caller operands receiver and result rather than bound positions`(): Unit {
        for (name in listOf("staticCall", "instanceCall", "staticExternal", "getter", "virtualAllocated", "bytesCall")) {
            val method = method(name, callOwner)
            for (at in method.instList.instructions.filter { it.callExpr != null })
                assertCallInputs(interp, method, at)
        }
        val caller = method("instanceCall", callOwner)
        val at = caller.instList.instructions.first { it.callExpr?.method?.method?.name == "instance" }
        val forms = interp.forms(key(caller))
        val receiver = AccessPathBase.Argument(0)
        val result = assertNotNull(accessPathBase(assertIs<JIRAssignInst>(at).lhv))
        assertIs<AccessPathBase.LocalVar>(result)
        assertTrue(checkNotNull(at.callExpr).args.none { accessPathBase(it) == receiver },
            "The receiver must be distinct from explicit call arguments")
        assertTrue(checkNotNull(at.callExpr).args.none { accessPathBase(it) == result },
            "The result must be absent from call operands")
        for (view in RuleView.entries) {
            assertTrue(forms.isBaseRelevant(Direction.FORWARD, at, receiver, view))
            assertTrue(forms.isBaseRelevant(Direction.BACKWARD, at, result, view))
        }
    }

    @Test fun `static read source observes ZERO and its lhs in both directions and views`(): Unit {
        val method = method("staticRead")
        val at = method.instList.instructions.filterIsInstance<JIRAssignInst>().first { it.rhv is JIRFieldRef }
        val rules = object : TaintRulesProvider by NoTaintRules {
            override fun sourceRulesForStaticField(field: JIRField, statement: CommonInst, fact: FactAp?, allRelevant: Boolean) =
                listOf(TaintStaticFieldSource(field, mkTrue(), listOf(AssignMark(TaintMark("READ"), Result)), null))
        }
        val owner = interp(rules)
        val lhs = assertNotNull(accessPathBase(at.lhv))
        val forms = owner.forms(key(method))
        for (view in RuleView.entries) {
            val forward = forms.statement(Direction.FORWARD, at, view)
            assertTrue(forward.edges.any { it.isSource && it.edge.from.base == AccessPathBase.Zero && it.edge.to.base == lhs })
            val backward = forms.statement(Direction.BACKWARD, at, view)
            assertTrue(backward.edges.any { it.isSource && it.edge.from.base == lhs })
            for (direction in Direction.entries) {
                assertTrue(forms.isBaseRelevant(direction, at, lhs, view))
                assertTrue(forms.isBaseRelevant(direction, at, AccessPathBase.Zero, view))
            }
        }
        assertStatementInputs(owner, method, at)
    }

    @Test fun `reverse field write includes alias destination that is not an instruction operand`(): Unit {
        val method = method("writeThroughFieldAlias", "sample.alias.HeapAliasSample")
        val at = method.instList.instructions.filterIsInstance<JIRAssignInst>().single { it.lhv is JIRFieldRef }
        val owner = interp(aliasParams = JIRLocalAliasAnalysis.Params(useAliasAnalysis = true))
        val forms = owner.forms(key(method))
        val alias = AccessPathBase.Argument(0)
        val rhs = assertNotNull(accessPathBase(at.rhv as JIRValue))
        for (view in RuleView.entries) {
            val forward = forms.statement(Direction.FORWARD, at, view)
            assertTrue(forward.edges.any { it.edge.from.base == rhs && it.edge.to.base == alias && it.edge.to.path.size == 2 })
            assertFalse(alias in forward.touched, "The alias is a generated target, not an ordinary write input")
            assertFalse(forms.isBaseRelevant(Direction.FORWARD, at, alias, view))
            val backward = forms.statement(Direction.BACKWARD, at, view)
            assertTrue(backward.edges.any { it.edge.from.base == alias && it.edge.to.base == rhs })
            assertTrue(forms.isBaseRelevant(Direction.BACKWARD, at, alias, view))
        }
        assertStatementInputs(owner, method, at)
    }

    @Test fun `reverse call includes persisted alias destination absent from direct bindings`(): Unit {
        val method = method("aliasOverwritten", callOwner)
        val at = method.instList.instructions.first { it.callExpr?.method?.method?.name == "external" }
        val owner = interp(aliasParams = JIRLocalAliasAnalysis.Params(useAliasAnalysis = true))
        val forms = owner.forms(key(method))
        val alias = AccessPathBase.Argument(0)
        assertTrue(checkNotNull(at.callExpr).args.none { accessPathBase(it) == alias })
        assertTrue(accessPathBase(assertIs<JIRAssignInst>(at).lhv) != alias)
        for (view in RuleView.entries) {
            val forward = forms.call(Direction.FORWARD, at, checkNotNull(at.callExpr), view)
            val aliases = forward.stages.filterIsInstance<CallStage.Edges>().filter { it.kind == StageKind.ALIASES }
            assertTrue(aliases.flatMap { it.summary.edges }.any { it.edge.to.base == alias })
            assertFalse(forms.isBaseRelevant(Direction.FORWARD, at, alias, view))
            val backward = forms.call(Direction.BACKWARD, at, checkNotNull(at.callExpr), view)
            assertTrue(backward.stages.filterIsInstance<CallStage.Edges>().any { stage ->
                stage.from == backward.entry && stage.summary.edges.any { it.edge.from.base == alias }
            })
            assertTrue(forms.isBaseRelevant(Direction.BACKWARD, at, alias, view))
        }
        assertCallInputs(owner, method, at)
    }

    @Test fun `base relevance does not load or specialize the call rules`(): Unit {
        val rules = CallRules()
        val method = method("instanceCall", callOwner)
        val at = method.instList.instructions.first { it.callExpr?.method?.method?.name == "instance" }
        val forms = interp(rules).forms(key(method))
        for (view in RuleView.entries) for (direction in Direction.entries) {
            assertTrue(forms.isBaseRelevant(direction, at, AccessPathBase.Argument(0), view))
            assertFalse(forms.isBaseRelevant(direction, at, unrelated, view))
        }
        assertTrue(rules.queries.isEmpty(), "A base footprint must not build the call plan")
        forms.call(Direction.FORWARD, at, checkNotNull(at.callExpr))
        assertTrue(rules.queries.isNotEmpty(), "The provider control must observe actual plan construction")
    }

    @Test fun `all physical method boundaries remain relevant for every base and view`(): Unit {
        val method = method("copy")
        val forms = interp.forms(key(method))
        val boundaries = method.instList.instructions.filterIsInstance<JMethodBoundaryInst>()
        assertEquals(3, boundaries.size)
        for (at in boundaries) for (view in RuleView.entries) for (direction in Direction.entries)
            for (base in listOf(AccessPathBase.Zero, AccessPathBase.Return, AccessPathBase.ClassStatic, unrelated))
                assertTrue(forms.isBaseRelevant(direction, at, base, view), "$direction/$view $base at $at")
    }
}
