package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyReferenceInstallFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlyReferenceInstallFuzzSample"
    private val ruleId = "baseonly-reference-install-fuzz"
    private val mark = "reference-install-taint"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    @TestFactory
    fun `Tree reference installations must survive BaseOnly summaries`(): List<DynamicTest> =
        samples.map { method ->
            DynamicTest.dynamicTest(method) {
                assertReachable(config, testClass, method, ruleId, "$method Tree control", ApMode.Tree)
                assertReachable(config, testClass, method, ruleId, "$method BaseOnly regression", ApMode.BaseOnlyField)
            }
        }

    private companion object {
        val samples = listOf(
            "constructorInstallThroughEnvelope",
            "constructorInstallThroughTwoEnvelopes",
        )
    }
}
