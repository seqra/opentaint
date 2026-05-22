package org.opentaint.semgrep.pattern.conversion.go

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.semgrep.pattern.SemgrepTaintPropagator
import org.opentaint.semgrep.pattern.conversion.IsMetavar
import org.opentaint.semgrep.pattern.conversion.MetavarAtom
import org.opentaint.semgrep.pattern.conversion.ParamCondition
import org.opentaint.semgrep.pattern.conversion.ParamConstraint
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternActionList
import org.opentaint.semgrep.pattern.conversion.TypeConstraint
import org.opentaint.semgrep.pattern.conversion.goNamed
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.test.assertTrue

class GoTaintRuleEmitterTest {

    private fun goPackage(pkg: String): TypeConstraint = goNamed(pkg)

    private fun listOfCall(call: SemgrepPatternAction): SemgrepPatternActionList =
        SemgrepPatternActionList(
            actions = listOf(call),
            hasEllipsisInTheEnd = false,
            hasEllipsisInTheBeginning = false,
        )

    private fun call(
        name: String,
        params: ParamConstraint = ParamConstraint.Concrete(emptyList()),
        obj: ParamCondition? = null,
        result: ParamCondition? = null,
        enclosing: TypeConstraint? = null,
    ): SemgrepPatternAction.MethodCall =
        SemgrepPatternAction.MethodCall(
            methodName = SignatureName.Concrete(name),
            result = result,
            params = params,
            obj = obj,
            enclosingClassName = enclosing,
        )

    private fun metavar(name: String): ParamCondition = IsMetavar(MetavarAtom.create(name))

    @Test
    fun `source taints the result of a named function`() {
        val emitter = GoTaintRuleEmitter()
        val list = listOfCall(call("Source", enclosing = goPackage("util")))

        val source = emitter.emitSource(list, "taint")

        assertEquals("util.Source", source?.function)
        assertEquals("taint", source?.mark)
        assertEquals(PositionBase.Result, source?.pos)
        assertTrue(emitter.dropped.isEmpty())
    }

    @Test
    fun `sink uses the argument position carrying the metavar`() {
        val emitter = GoTaintRuleEmitter()
        val list = listOfCall(
            call(
                "Sink",
                params = ParamConstraint.Concrete(listOf(metavar("\$X"))),
                enclosing = goPackage("util"),
            ),
        )

        val sink = emitter.emitSink(list, "taint", "r")

        assertEquals("util.Sink", sink?.function)
        assertEquals(PositionBase.Argument(0), sink?.pos)
        assertEquals("r", sink?.id)
        assertTrue(emitter.dropped.isEmpty())
    }

    @Test
    fun `sink picks the second argument when only it carries the metavar`() {
        val emitter = GoTaintRuleEmitter()
        val list = listOfCall(
            call(
                "Exec",
                params = ParamConstraint.Concrete(listOf(ParamCondition.True, metavar("\$Q"))),
                enclosing = goPackage("db"),
            ),
        )

        val sink = emitter.emitSink(list, "taint", "r")

        assertEquals("db.Exec", sink?.function)
        assertEquals(PositionBase.Argument(1), sink?.pos)
    }

    @Test
    fun `sink falls back to receiver when only the object carries the metavar`() {
        val emitter = GoTaintRuleEmitter()
        // ($X).Sink(...) -> the receiver is the tainted position
        val list = listOfCall(
            call(
                "Sink",
                params = ParamConstraint.Concrete(emptyList()),
                obj = metavar("\$X"),
            ),
        )

        val sink = emitter.emitSink(list, "taint", "r")

        assertEquals("Sink", sink?.function)
        assertEquals(PositionBase.This, sink?.pos)
    }

    @Test
    fun `sink with no tainted position is dropped and counted`() {
        val emitter = GoTaintRuleEmitter()
        val list = listOfCall(
            call(
                "Sink",
                params = ParamConstraint.Concrete(listOf(ParamCondition.True)),
                enclosing = goPackage("util"),
            ),
        )

        assertNull(emitter.emitSink(list, "taint", "r"))
        assertEquals(1, emitter.dropped["sink_no_tainted_position"])
    }

    @Test
    fun `source on a non-single-call action list is dropped and counted`() {
        val emitter = GoTaintRuleEmitter()
        val twoActions = SemgrepPatternActionList(
            actions = listOf(
                call("Source", enclosing = goPackage("util")),
                SemgrepPatternAction.MethodExit(emptyList()),
            ),
            hasEllipsisInTheEnd = false,
            hasEllipsisInTheBeginning = false,
        )

        assertNull(emitter.emitSource(twoActions, "taint"))
        assertEquals(1, emitter.dropped["source_not_single_call"])
    }

    @Test
    fun `unnameable source (metavar method name) is dropped and counted`() {
        val emitter = GoTaintRuleEmitter()
        val list = listOfCall(
            SemgrepPatternAction.MethodCall(
                methodName = SignatureName.MetaVar("\$F"),
                result = null,
                params = ParamConstraint.Concrete(emptyList()),
                obj = null,
                enclosingClassName = goPackage("util"),
            ),
        )

        assertNull(emitter.emitSource(list, "taint"))
        assertEquals(1, emitter.dropped["source_unnameable"])
    }

    @Test
    fun `pass maps from-argument to result`() {
        val emitter = GoTaintRuleEmitter()
        // wrap(from=$IN -> to=$OUT) modeled as $OUT = pkg.Wrap($IN)
        val pattern = listOfCall(
            call(
                "Wrap",
                params = ParamConstraint.Concrete(listOf(metavar("\$IN"))),
                result = metavar("\$OUT"),
                enclosing = goPackage("pkg"),
            ),
        )
        val prop = SemgrepTaintPropagator(
            from = "\$IN",
            to = "\$OUT",
            bySideEffect = null,
            pattern = pattern,
        )

        val pass = emitter.emitPass(prop)

        assertEquals("pkg.Wrap", pass?.function)
        assertEquals(PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(0)), pass?.from)
        assertEquals(PositionBaseWithModifiers.BaseOnly(PositionBase.Result), pass?.to)
        assertTrue(emitter.dropped.isEmpty())
    }

    @Test
    fun `pass with an unlocatable metavar is dropped and counted`() {
        val emitter = GoTaintRuleEmitter()
        val pattern = listOfCall(
            call(
                "Wrap",
                params = ParamConstraint.Concrete(listOf(metavar("\$IN"))),
                result = metavar("\$OUT"),
                enclosing = goPackage("pkg"),
            ),
        )
        val prop = SemgrepTaintPropagator(
            from = "\$IN",
            to = "\$MISSING",
            bySideEffect = null,
            pattern = pattern,
        )

        assertNull(emitter.emitPass(prop))
        assertEquals(1, emitter.dropped["pass_to_not_found"])
    }
}
