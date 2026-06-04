package org.opentaint.go.sast.dataflow

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
class GenericsTest : AnalysisTest() {

    private val intSource = GoSerializedRule.Source(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("SourceInt"),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
    )
    private val intSink = GoSerializedRule.Sink(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("SinkInt"),
        condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = GoSinkMetaData("Taint sink: test/util.SinkInt"),
        info = null,
    )

    // Generic identity function
    @Test fun genericFunc001T() = assertReachable("test.genericFunc001T")
    @Test fun genericFunc002F() = assertNotReachable("test.genericFunc002F")
    @Test fun genericFuncInt001T() = assertSinkReachable(intSource, intSink, "test.genericFuncInt001T")

    // Generic box container
    @Test fun genericBox001T() = assertReachable("test.genericBox001T")
    @Test fun genericBox002F() = assertNotReachable("test.genericBox002F")
    @Test fun genericBoxSet001T() = assertReachable("test.genericBoxSet001T")

    // Generic pair
    @Test fun genericPair001T() = assertReachable("test.genericPair001T")
    @Test fun genericPair002F() = assertNotReachable("test.genericPair002F")
}
