package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedPassAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class PassThroughTest : AnalysisTest() {

    private val passthroughRule = GoSerializedRule.PassThrough(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("Passthrough"),
        copy = listOf(
            GoSerializedPassAction(
                from = PositionBaseWithModifiers.BaseOnly(Argument(0)),
                to = PositionBaseWithModifiers.BaseOnly(Result),
            ),
        ),
        info = null,
    )

    private val transformRule = GoSerializedRule.PassThrough(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("Transform"),
        copy = listOf(
            GoSerializedPassAction(
                from = PositionBaseWithModifiers.BaseOnly(Argument(0)),
                to = PositionBaseWithModifiers.BaseOnly(Result),
            ),
        ),
        info = null,
    )

    @Test fun passThrough001T() {
        val vulns = runAnalysis(stdSource, stdSink, "test.passThrough001T", extraPassRules = listOf(passthroughRule))
        assertTrue(vulns.isNotEmpty(), "Sink was not reached in test.passThrough001T")
    }

    @Test fun passThrough002F() {
        // No pass rule for sanitize() → call kills taint
        val vulns = runAnalysis(stdSource, stdSink, "test.passThrough002F")
        assertTrue(vulns.isEmpty(), "Sink should not be reached in test.passThrough002F")
    }

    @Test fun passThrough003T() {
        val vulns = runAnalysis(stdSource, stdSink, "test.passThrough003T", extraPassRules = listOf(transformRule))
        assertTrue(vulns.isNotEmpty(), "Sink was not reached in test.passThrough003T")
    }
}
