package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyTraceProjectionFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true

    private val testClass = "test.samples.BaseOnlyTraceProjectionFuzzSample"
    private val ruleId = "base-only-trace-projection-fuzz"
    private val mark = "trace-projection-taint"
    private val config = SerializedTaintConfig(
        source = listOf(wholeObjectSourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    @TestFactory
    fun `Tree traces rejected by BaseOnly projection trace resolution`(): List<DynamicTest> =
        samples.map { method ->
            DynamicTest.dynamicTest(method) {
                assertReachable(config, testClass, method, ruleId, "$method Tree control", ApMode.Tree)
                assertReachable(config, testClass, method, ruleId, "$method BaseOnly trace candidate", ApMode.BaseOnlyField)
            }
        }

    private companion object {
        val samples = listOf(
            "projectOneLevel",
            "projectThreeLevels",
            "relayThenProject",
            "mutateThenProject",
        )
    }
}
