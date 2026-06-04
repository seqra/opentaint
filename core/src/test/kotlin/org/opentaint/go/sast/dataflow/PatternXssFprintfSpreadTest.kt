package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.Sink
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class PatternXssFprintfSpreadTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    private val fprintfSink = Sink(
        pkg = GoNameMatcher.Simple("test"),
        function = GoNameMatcher.Simple("fprintfStub"),
        condition = GoSerializedCondition.ContainsMark(
            "taint",
            PositionBaseWithModifiers.BaseOnly(Argument(1)),
        ),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = GoSinkMetaData("Taint sink: test.fprintfStub"),
        info = null,
    )

    @Test
    fun queryUnescapeFprintfSpread001T() {
        val vulns = runAnalysis(stdSource, fprintfSink, "test.queryUnescapeFprintfSpread001T")
        assertTrue(vulns.isNotEmpty(), "Sink was not reached in queryUnescapeFprintfSpread001T")
    }

    @Test
    fun queryUnescapeFprintfSpread002F() {
        val vulns = runAnalysis(stdSource, fprintfSink, "test.queryUnescapeFprintfSpread002F")
        assertTrue(vulns.isEmpty(), "Sink should not be reached in queryUnescapeFprintfSpread002F")
    }
}
