package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SpringPetclinicGetterRegressionTest : AnalysisTest() {
    companion object {
        private const val TEST_CLASS = "test.samples.SpringPetclinicGetterRegressionSample"
        private const val TAINT_MARK = "spring-petclinic-owner"
        private const val RULE_ID = "spring-petclinic-getter-flow"
    }

    override val sourceFileExtension: String = "java"
    override val useSpringRuleProvider: Boolean = true
    override val useDefaultUnrollStrategy: Boolean = true

    @Test
    fun `whole receiver taint propagates through getter field`() {
        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(TEST_CLASS, "wholeReceiverThroughGetter", TAINT_MARK, 0)),
            sink = listOf(sinkRule(TEST_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
        )

        assertReachable(
            config = config,
            testCls = TEST_CLASS,
            entryPointName = "wholeReceiverThroughGetter",
            ruleId = RULE_ID,
            testName = "spring-petclinic whole receiver through getter Tree control",
            apMode = ApMode.Tree
        )
        assertReachable(
            config = config,
            testCls = TEST_CLASS,
            entryPointName = "wholeReceiverThroughGetter",
            ruleId = RULE_ID,
            testName = "spring-petclinic whole receiver through getter BaseOnly",
            apMode = ApMode.BaseOnlyField
        )
    }
}
