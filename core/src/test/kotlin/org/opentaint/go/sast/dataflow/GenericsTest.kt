package org.opentaint.go.sast.dataflow

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
class GenericsTest : AnalysisTest() {

    private val intSource = TaintRules.Source(
        function = "test/util.SourceInt",
        condition = mkTrue(),
        actionsAfter = listOf(GoAssignMark("taint", PositionBaseWithModifiers.BaseOnly(Result))),
    )
    private val intSink = TaintRules.Sink(
        function = "test/util.SinkInt",
        condition = CommonCondition.Atom(GoRuleCondition.ContainsMark(PositionBaseWithModifiers.BaseOnly(Argument(0)), "taint")),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = TaintRules.Sink.DefaultMeta("Taint sink: test/util.SinkInt"),
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
