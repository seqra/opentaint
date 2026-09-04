package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyTraceResolutionFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlyTraceRelayFuzzSample"
    private val ruleId = "base-only-trace-resolution-fuzz"
    private val mark = "trace-resolution-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    @TestFactory
    fun `Tree traces rejected by BaseOnly trace resolution`(): List<DynamicTest> =
        samples.map { method ->
            DynamicTest.dynamicTest(method) {
                assertReachable(config, testClass, method, ruleId, "$method Tree control", ApMode.Tree)
                assertReachable(config, testClass, method, ruleId, "$method BaseOnly trace regression", ApMode.BaseOnlyField)
            }
        }

    private companion object {
        val samples = listOf(
            "returnThroughIdentity",
            "returnThroughDoubleIdentity",
            "returnThroughInstanceIdentity",
            "returnThroughInterfaceIdentity",
            "returnThroughBranchIdentity",
            "returnOuterThroughIdentity",
        )
    }
}
