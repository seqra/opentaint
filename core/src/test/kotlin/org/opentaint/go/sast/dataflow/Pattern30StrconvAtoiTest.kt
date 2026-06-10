package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.Sink
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.Source
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Pattern30StrconvAtoiTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    private val intSink = Sink(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("SinkInt"),
        condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = GoSinkMetaData("Taint sink: test/util.SinkInt"),
        info = null,
    )

    @Test
    fun strconvAtoi001T() = assertSinkReachable(stdSource, intSink, "test.strconvAtoi001T")

    @Test
    fun strconvAtoi002F() = assertSinkNotReachable(stdSource, intSink, "test.strconvAtoi002F")
}
