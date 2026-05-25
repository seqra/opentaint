package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.go.rules.GoAssignMark
import org.opentaint.dataflow.go.rules.GoRuleCondition
import org.opentaint.dataflow.go.rules.TaintRules
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class TypeOpsTest : AnalysisTest() {

    private val intSource = TaintRules.Source(
        function = "test/util.SourceInt",
        condition = mkTrue(),
        actionsAfter = listOf(GoAssignMark("taint", PositionBaseWithModifiers.BaseOnly(Result))),
    )
    private val floatSink = TaintRules.Sink(
        function = "test/util.SinkFloat",
        condition = CommonCondition.Atom(GoRuleCondition.ContainsMark(PositionBaseWithModifiers.BaseOnly(Argument(0)), "taint")),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = TaintRules.Sink.DefaultMeta("Taint sink: test/util.SinkFloat"),
    )
    private val anySource = TaintRules.Source(
        function = "test/util.SourceAny",
        condition = mkTrue(),
        actionsAfter = listOf(GoAssignMark("taint", PositionBaseWithModifiers.BaseOnly(Result))),
    )

    // Type conversion
    @Test fun typeCastInt001T() = assertSinkReachable(intSource, floatSink, "test.typeCastInt001T")
    @Test fun typeCastInt002F() = assertSinkNotReachable(intSource, floatSink, "test.typeCastInt002F")

    // String to bytes and back
    @Test fun typeCastStringToBytes001T() = assertReachable("test.typeCastStringToBytes001T")
    @Test fun typeCastStringToBytes002F() = assertNotReachable("test.typeCastStringToBytes002F")

    // Interface wrapping
    @Test fun interfaceWrap001T() = assertReachable("test.interfaceWrap001T")
    @Test fun interfaceWrap002F() = assertNotReachable("test.interfaceWrap002F")

    // Type assertion
    @Test fun typeAssert001T() = assertSinkReachable(anySource, stdSink, "test.typeAssert001T")
    @Test fun typeAssert002F() = assertSinkNotReachable(anySource, stdSink, "test.typeAssert002F")

    // Type assertion with comma-ok (tuple extraction) — abstract refinement doesn't propagate target fact for non-call tuples
    @Disabled("CommaOk type assertion tuple extraction: abstract refinement path incomplete")
    @Test fun typeAssertOk001T() = assertSinkReachable(anySource, stdSink, "test.typeAssertOk001T")
    @Test fun typeAssertOk002F() = assertSinkNotReachable(anySource, stdSink, "test.typeAssertOk002F")

    // Rune conversion
    @Test fun runeConv001T() = assertSinkReachable(intSource, stdSink, "test.runeConv001T")
    @Test fun runeConv002F() = assertSinkNotReachable(intSource, stdSink, "test.runeConv002F")
}
