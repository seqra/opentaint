package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParsingResult
import org.opentaint.semgrep.go.pattern.conversion.GoConcreteType
import org.opentaint.semgrep.go.pattern.conversion.GoPatternToActionListConverter
import org.opentaint.semgrep.go.pattern.conversion.goNamed
import org.opentaint.semgrep.go.pattern.conversion.goQualified
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.SemgrepTraceEntry.Step
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.ClassConstraint
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.ConstructorCall
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.MethodCall
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.MethodExit
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.MethodSignature
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureName
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class PatternToActionListConverterTest {
    private val parser = SemgrepGoPatternParser()
    private val noopTrace = SemgrepRuleLoadStepTrace(Step.BUILD_PARSE_SEMGREP_RULE)

    private fun parse(src: String): SemgrepGoPattern {
        val r = parser.parseSemgrepGoPattern(src)
        check(r is SemgrepGoPatternParsingResult.Ok) { "parse failed for `$src`: $r" }
        return r.pattern
    }

    private fun convert(src: String): Pair<SemgrepPatternActionList?, Map<String, Int>> {
        val c = GoPatternToActionListConverter()
        return c.createActionList(parse(src), noopTrace) to c.failedTransformations
    }

    private fun convertOk(src: String): SemgrepPatternActionList {
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
        assertEquals(goNamed("fmt"), call.enclosingClassName)
        assertEquals(ParamCondition.True, call.obj)
        assertEquals(
            ParamConstraint.Concrete(listOf(IsMetavar(MetavarAtom.create("\$X")))),
            call.params,
        )
    }

    @Test fun methodCallOnMetavarReceiverWithEllipsisArgs() {
        val a = convertOk("\$DB.Exec(\$QUERY, ...)")
        val call = a.actions.single() as MethodCall
        assertEquals(SignatureName.Concrete("Exec"), call.methodName)
        assertEquals(IsMetavar(MetavarAtom.create("\$DB")), call.obj)
        assertEquals(null, call.enclosingClassName)
        val params = call.params as ParamConstraint.Partial
        assertEquals(
            listOf(ParamPattern(ParamPosition.Concrete(0), IsMetavar(MetavarAtom.create("\$QUERY")))),
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

    @Test fun nestedCallArgumentLinearizes() {
        val a = convertOk("outer(inner(\$X))")
        assertEquals(2, a.actions.size)
        val inner = a.actions[0] as MethodCall
        val outer = a.actions[1] as MethodCall
        assertEquals(SignatureName.Concrete("inner"), inner.methodName)
        assertEquals(SignatureName.Concrete("outer"), outer.methodName)
        val innerResult = inner.result as IsMetavar
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

    @Test fun shortVarDeclBindsResult() {
        val a = convertOk("\$X := getInput()")
        val call = a.actions.single() as MethodCall
        assertEquals(SignatureName.Concrete("getInput"), call.methodName)
        assertEquals(IsMetavar(MetavarAtom.create("\$X")), call.result)
    }

    @Test fun assignBindsResult() {
        val a = convertOk("\$X = source.Read()")
        val call = a.actions.single() as MethodCall
        assertEquals(IsMetavar(MetavarAtom.create("\$X")), call.result)
    }

    @Test fun multiLhsAssignFailsGracefully() {
        val (r, failures) = convert("\$A, \$B := f()")
        assertNull(r)
        assertTrue(failures.keys.any { it.contains("multi") }, "expected a multi-LHS failure reason, got $failures")
    }

    @Test fun keyedCompositeLiteral() {
        val a = convertOk("http.Cookie{Secure: true, ...}")
        val ctor = a.actions.single() as ConstructorCall
        assertEquals(goQualified("http", "Cookie"), ctor.className)
        val params = ctor.params as ParamConstraint.Partial
        assertEquals(
            listOf(ParamPattern(ParamPosition.Named("Secure"), SpecificBoolValue(true))),
            params.params,
        )
    }

    @Test fun pointerCompositeLiteralInAssignment() {
        val a = convertOk("\$C := &http.Client{...}")
        val ctor = a.actions.single() as ConstructorCall
        assertEquals(goQualified("http", "Client"), ctor.className)
        assertEquals(IsMetavar(MetavarAtom.create("\$C")), ctor.result)
    }

    @Test fun funcDeclEmitsSignatureThenBody() {
        val a = convertOk("func \$H(\$E \$T) { sink(\$E) }")
        val sig = a.actions[0] as MethodSignature
        assertEquals(SignatureName.MetaVar("\$H"), sig.methodName)
        assertNull(sig.enclosingClassMetavar)
        assertTrue(sig.enclosingClassConstraints.isEmpty())
        assertEquals(
            listOf(
                ParamPattern(ParamPosition.Concrete(0), IsMetavar(MetavarAtom.create("\$E"))),
                ParamPattern(ParamPosition.Concrete(0), ParamCondition.TypeIs(TypeConstraint.MetaVar("\$T"))),
            ),
            sig.params.params,
        )
        assertTrue(a.actions[1] is MethodCall)
    }

    @Test fun funcDeclSequenceWithTrailingCall() {
        val a = convertOk("func \$H(\$E \$T, ...) {...}\n...\nlambda.Start(\$H, ...)")
        assertTrue(a.actions.first() is MethodSignature)
        assertTrue(a.actions.last() is MethodCall)
        assertEquals(SignatureName.Concrete("Start"), (a.actions.last() as MethodCall).methodName)
    }

    @Test fun returnEmitsMethodExit() {
        val a = convertOk("func \$F() { return \$X }")
        val exit = a.actions.last() as MethodExit
        assertEquals(listOf(IsMetavar(MetavarAtom.create("\$X"))), exit.retVals)
    }

    @Test fun returnCallLinearizesAndDoesNotCrash() {
        val a = convertOk("func \$F() { return sink(\$X) }")
        // [MethodSignature, MethodCall(sink) -> $art, MethodExit([$art])]
        val call = a.actions.first { it is MethodCall } as MethodCall
        assertEquals(SignatureName.Concrete("sink"), call.methodName)
        val exit = a.actions.last() as MethodExit
        val callResult = call.result as IsMetavar
        assertEquals(listOf<ParamCondition>(callResult), exit.retVals)
        assertTrue((callResult.metavar as MetavarAtom.Basic).isArtificial)
    }

    @Test fun methodDeclWithConcreteReceiverPopulatesClassConstraints() {
        val a = convertOk("func (\$R *Foo) Bar() {}")
        val sig = a.actions.single() as MethodSignature
        assertEquals(SignatureName.Concrete("Bar"), sig.methodName)
        assertNull(sig.enclosingClassMetavar)
        val expectedType = TypeConstraint.Concrete(GoConcreteType.Pointer(goNamed("Foo")))
        assertEquals(
            listOf(ClassConstraint.SuperType(expectedType)),
            sig.enclosingClassConstraints,
        )
    }
}
