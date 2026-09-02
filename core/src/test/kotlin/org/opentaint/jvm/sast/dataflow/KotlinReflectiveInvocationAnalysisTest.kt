package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class KotlinReflectiveInvocationAnalysisTest : AnalysisTest() {

    companion object {
        private const val SAMPLE_CLASS = "test.samples.KotlinReflectiveInvocationSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "kt-reflective-invocation-rule"
    }

    override val sourceFileExtension: String = "kt"
    override val useDefaultConfig: Boolean = true

    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(SAMPLE_CLASS, "source", TAINT_MARK)),
        sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    @Test
    fun `control - a direct call to the target reaches the sink`() {
        assertReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "directInvocationFlow",
            ruleId = RULE_ID,
            testName = "kotlin direct invocation"
        )
    }

    @Test
    fun `getMethod with a constant name resolves to the leaking target`() {
        assertReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "reflectiveLeakFlow",
            ruleId = RULE_ID,
            testName = "kotlin reflective leak"
        )
    }

    @Test
    fun `a constant name selecting a dropping target does not reach the sink`() {
        assertNotReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "reflectiveDropFlow",
            testName = "kotlin reflective drop"
        )
    }

    @Test
    fun `an unresolvable name is reported as a resolution failure and is not redirected`() {
        assertNotReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "reflectiveUnresolvedFlow",
            testName = "kotlin reflective unresolved"
        )
    }
}
