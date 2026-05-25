package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.go.rules.CopyData
import org.opentaint.dataflow.go.rules.Position
import org.opentaint.dataflow.go.rules.TaintRules
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SanitizationPatternTest : AnalysisTest() {
    private val passthroughRule = TaintRules.PassThrough(
        function = "test/util.Passthrough",
        actionsAfter = listOf(CopyData(Position.Argument(0), Position.Result)),
    )

    // Conservative: only one branch sanitizes, so taint persists
    @Test fun sanitizeConditional001T() = assertReachable("test.sanitizeConditional001T")
    @Test fun sanitizeConditional002F() = assertNotReachable("test.sanitizeConditional002F")

    @Test fun sanitizeReturn001T() = assertReachable("test.sanitizeReturn001T")
    @Test fun sanitizeReturn002F() = assertNotReachable("test.sanitizeReturn002F")

    @Test
    fun sanitizeChain001T() {
        val vulnerabilities = runAnalysis(stdSource, stdSink, "test.sanitizeChain001T", extraPassRules = listOf(passthroughRule))
        assertTrue(vulnerabilities.isNotEmpty(), "Sink was not reached in ${"test.sanitizeChain001T"}")
    }

    @Test fun sanitizeChain002F() = assertNotReachable("test.sanitizeChain002F")

    @Test fun sanitizeReassign001T() = assertReachable("test.sanitizeReassign001T")
    @Test fun sanitizeReassign002F() = assertNotReachable("test.sanitizeReassign002F")
}
