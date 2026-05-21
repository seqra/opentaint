package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.SemgrepGoPattern
import org.opentaint.semgrep.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.pattern.SemgrepGoPatternParsingResult
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.MethodCall
import org.opentaint.semgrep.pattern.conversion.SemgrepGoPatternAction.SignatureName
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class PatternToActionListConverterTest {
    private val parser = SemgrepGoPatternParser()

    private fun parse(src: String): SemgrepGoPattern {
        val r = parser.parseSemgrepGoPattern(src)
        check(r is SemgrepGoPatternParsingResult.Ok) { "parse failed for `$src`: $r" }
        return r.pattern
    }

    private fun convert(src: String): Pair<SemgrepGoPatternActionList?, Map<String, Int>> {
        val c = PatternToActionListConverter()
        return c.createActionList(parse(src)) to c.failedTransformations
    }

    private fun convertOk(src: String): SemgrepGoPatternActionList {
        val (r, failures) = convert(src)
        assertNotNull(r, "conversion failed for `$src`: $failures")
        return r
    }

    @Test fun unsupportedReturnsNullAndRecordsReason() {
        val (result, failures) = convert("if true { }")
        assertNull(result)
        assertTrue(failures.isNotEmpty(), "expected a recorded failure reason, got $failures")
    }

    @Test fun packageQualifiedCall() {
        val a = convertOk("fmt.Println(\$X)")
        assertEquals(1, a.actions.size)
        val call = a.actions.single() as MethodCall
        assertEquals(SignatureName.Concrete("Println"), call.methodName)
        assertEquals(TypePattern.Named("fmt"), call.enclosingClassName)
        assertEquals(ParamCondition.True, call.obj)
        assertEquals(
            ParamConstraint.Concrete(listOf(ParamCondition.IsMetavar(MetavarAtom.create("X")))),
            call.params,
        )
    }

    @Test fun methodCallOnMetavarReceiverWithEllipsisArgs() {
        val a = convertOk("\$DB.Exec(\$QUERY, ...)")
        val call = a.actions.single() as MethodCall
        assertEquals(SignatureName.Concrete("Exec"), call.methodName)
        assertEquals(ParamCondition.IsMetavar(MetavarAtom.create("DB")), call.obj)
        assertEquals(null, call.enclosingClassName)
        val params = call.params as ParamConstraint.Partial
        assertEquals(
            listOf(ParamPattern(ParamPosition.Concrete(0), ParamCondition.IsMetavar(MetavarAtom.create("QUERY")))),
            params.params,
        )
    }

    @Test fun plainCallWithStringEllipsis() {
        val a = convertOk("sink(\"...\")")
        val call = a.actions.single() as MethodCall
        assertEquals(SignatureName.Concrete("sink"), call.methodName)
        assertEquals(null, call.obj)
        assertEquals(ParamConstraint.Concrete(listOf(ParamCondition.AnyStringLiteral)), call.params)
    }

    @Test fun chainedCallLinearizes() {
        val a = convertOk("a.b().c()")
        assertEquals(2, a.actions.size)
        val inner = a.actions[0] as MethodCall
        val outer = a.actions[1] as MethodCall
        assertEquals(SignatureName.Concrete("b"), inner.methodName)
        assertEquals(SignatureName.Concrete("c"), outer.methodName)
        // inner.result is an artificial metavar that becomes outer.obj
        val innerResult = inner.result as ParamCondition.IsMetavar
        assertEquals(innerResult, outer.obj)
        assertTrue((innerResult.metavar as MetavarAtom.Basic).isArtificial)
    }

    @Test fun nestedCallArgumentLinearizes() {
        val a = convertOk("outer(inner(\$X))")
        assertEquals(2, a.actions.size)
        val inner = a.actions[0] as MethodCall
        val outer = a.actions[1] as MethodCall
        assertEquals(SignatureName.Concrete("inner"), inner.methodName)
        assertEquals(SignatureName.Concrete("outer"), outer.methodName)
        val innerResult = inner.result as ParamCondition.IsMetavar
        assertEquals(ParamConstraint.Concrete(listOf(innerResult)), outer.params)
    }

    @Test fun bareEllipsisHasBothFlags() {
        val a = convertOk("...")
        assertTrue(a.actions.isEmpty())
        assertTrue(a.hasEllipsisInTheBeginning)
        assertTrue(a.hasEllipsisInTheEnd)
    }

    @Test fun sequenceWithEllipsisSeparator() {
        val a = convertOk("\$DB.Exec(\$Q, ...)\n...\n\$DB.Close()")
        assertEquals(2, a.actions.size)
        assertTrue(a.actions[0] is MethodCall && (a.actions[0] as MethodCall).methodName == SignatureName.Concrete("Exec"))
        assertTrue(a.actions[1] is MethodCall && (a.actions[1] as MethodCall).methodName == SignatureName.Concrete("Close"))
        assertEquals(false, a.hasEllipsisInTheBeginning)
        assertEquals(false, a.hasEllipsisInTheEnd)
    }

    @Test fun leadingEllipsisSetsBeginningFlag() {
        val a = convertOk("...\nrand.Read(\$X)")
        assertEquals(1, a.actions.size)
        assertTrue(a.hasEllipsisInTheBeginning)
        assertEquals(false, a.hasEllipsisInTheEnd)
    }

    @Test fun deferUnwrapsToCall() {
        val a = convertOk("defer \$F.Close()")
        val call = a.actions.single() as MethodCall
        assertEquals(SignatureName.Concrete("Close"), call.methodName)
    }
}
