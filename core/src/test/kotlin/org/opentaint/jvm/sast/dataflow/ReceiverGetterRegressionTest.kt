package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ReceiverGetterRegressionTest : AnalysisTest() {
    companion object {
        private const val TEST_CLASS = "test.samples.ReceiverGetterRegressionSample"
        private const val TAINT_MARK = "receiver-getter-taint"
        private const val RULE_ID = "receiver-getter-flow"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true

    @Test
    fun `whole receiver taint propagates through getter field`() {
        val config = SerializedTaintConfig(
            source = listOf(wholeObjectSourceRule(TEST_CLASS, "source", TAINT_MARK)),
            sink = listOf(sinkRule(TEST_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
        )

        assertReachable(
            config = config,
            testCls = TEST_CLASS,
            entryPointName = "wholeReceiverThroughGetter",
            ruleId = RULE_ID,
            testName = "whole receiver through getter Tree control",
            apMode = ApMode.Tree
        )
        assertReachable(
            config = config,
            testCls = TEST_CLASS,
            entryPointName = "wholeReceiverThroughGetter",
            ruleId = RULE_ID,
            testName = "whole receiver through getter BaseOnly regression",
            apMode = ApMode.BaseOnlyField
        )
    }
}
