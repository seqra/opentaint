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
class SanitizationPatternTest : AnalysisTest() {
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
