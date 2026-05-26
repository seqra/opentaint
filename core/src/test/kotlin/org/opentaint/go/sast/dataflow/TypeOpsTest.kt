package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class TypeOpsTest : AnalysisTest() {

    private val intSource = GoSerializedRule.Source(
        function = GoNameMatcher.Simple("test/util.SourceInt"),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
    )
    private val floatSink = GoSerializedRule.Sink(
        function = GoNameMatcher.Simple("test/util.SinkFloat"),
        condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = GoSinkMetaData("Taint sink: test/util.SinkFloat"),
        info = null,
    )
    private val anySource = GoSerializedRule.Source(
        function = GoNameMatcher.Simple("test/util.SourceAny"),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
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
