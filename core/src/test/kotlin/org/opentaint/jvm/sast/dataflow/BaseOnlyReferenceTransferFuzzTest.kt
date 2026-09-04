package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class BaseOnlyReferenceTransferFuzzTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"

    private val testClass = "test.samples.BaseOnlyReferenceTransferFuzzSample"
    private val ruleId = "base-only-reference-transfer-fuzz"
    private val mark = "reference-transfer-source"
    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(testClass, "source", mark)),
        sink = listOf(sinkRule(testClass, "sink", ruleId, listOf(Argument(0) to mark))),
    )

    private val cases = listOf(
        "nestedEnvelopeConstructors", "tripleNestedConstructors", "envelopeFactory",
        "envelopeFactoryFromValue", "outerFactoryFromValue", "envelopeSetterAfterPayloadConstructor",
        "envelopeSetterAfterPayloadSetter", "fluentNestedEnvelope",
        "referenceArrayWrapper",
    )

    @TestFactory
    fun `Tree reference transfers omitted by BaseOnly forward analysis`() = cases.map { method ->
        DynamicTest.dynamicTest(method) {
            assertReachable(config, testClass, method, ruleId, "$method Tree control", ApMode.Tree)
            assertReachable(config, testClass, method, ruleId, "$method BaseOnlyField forward regression", ApMode.BaseOnlyField)
        }
    }
}
