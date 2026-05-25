package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.go.rules.CopyData
import org.opentaint.dataflow.go.rules.Position
import org.opentaint.dataflow.go.rules.TaintRules
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class PassThroughTest : AnalysisTest() {

    private val passthroughRule = TaintRules.PassThrough(
        function = "test/util.Passthrough",
        actionsAfter = listOf(CopyData(Position.Argument(0), Position.Result)),
    )

    private val transformRule = TaintRules.PassThrough(
        function = "test/util.Transform",
        actionsAfter = listOf(CopyData(Position.Argument(0), Position.Result)),
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
