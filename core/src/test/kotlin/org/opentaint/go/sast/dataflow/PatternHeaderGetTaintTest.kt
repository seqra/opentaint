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
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers.WithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier.ArrayElement
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class PatternHeaderGetTaintTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    private val headerSource = Source(
        pkg = GoNameMatcher.Simple("test"),
        function = GoNameMatcher.Simple("sourceHeader"),
        condition = null,
        taint = listOf(
            GoSerializedAssignAction("taint", WithModifiers(Result, listOf(ArrayElement, ArrayElement))),
        ),
        info = null,
    )

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
    fun headerGetSinkDirect001T() {
        val vulns = runAnalysis(headerSource, stdSink, "test.headerGetSink001T")
        assertTrue(vulns.isNotEmpty(), "Sink was not reached in headerGetSink001T")
    }

    @Test
    fun headerGetFprintf001T() {
        val vulns = runAnalysis(headerSource, fprintfSink, "test.headerGetFprintf001T")
        assertTrue(vulns.isNotEmpty(), "Sink was not reached in headerGetFprintf001T")
    }
}
