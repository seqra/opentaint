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
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("SourceInt"),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
    )
    private val floatSink = GoSerializedRule.Sink(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("SinkFloat"),
        condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = GoSinkMetaData("Taint sink: test/util.SinkFloat"),
        info = null,
    )
    private val anySource = GoSerializedRule.Source(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("SourceAny"),
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

    // Type assertion with comma-ok (tuple extraction)
    @Test fun typeAssertOk001T() = assertSinkReachable(anySource, stdSink, "test.typeAssertOk001T")
    @Test fun typeAssertOk002F() = assertSinkNotReachable(anySource, stdSink, "test.typeAssertOk002F")

    // Rune conversion
    @Test fun runeConv001T() = assertSinkReachable(intSource, stdSink, "test.runeConv001T")
    @Test fun runeConv002F() = assertSinkNotReachable(intSource, stdSink, "test.runeConv002F")

    // ── Pattern 4: type-assert on chained expression — all variants PASS today
    @Test fun typeAssertOnMapElem001T() = assertReachable("test.typeAssertOnMapElem001T")
    @Test fun typeAssertOnMapElem002F() = assertNotReachable("test.typeAssertOnMapElem002F")

    @Test fun typeAssertOnFieldRead001T() = assertReachable("test.typeAssertOnFieldRead001T")
    @Test fun typeAssertOnFieldRead002F() = assertNotReachable("test.typeAssertOnFieldRead002F")

    @Test fun typeAssertOnCallResult001T() = assertReachable("test.typeAssertOnCallResult001T")
    @Test fun typeAssertOnCallResult002F() = assertNotReachable("test.typeAssertOnCallResult002F")

    // ── Pattern 5: type-switch with case binding + outer-var reassign
    @Test fun typeSwitchBinding001T() = assertReachable("test.typeSwitchBinding001T")
    @Test fun typeSwitchBinding002F() = assertNotReachable("test.typeSwitchBinding002F")
}
