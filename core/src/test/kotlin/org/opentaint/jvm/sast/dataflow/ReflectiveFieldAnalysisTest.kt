package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ReflectiveFieldAnalysisTest : AnalysisTest() {

    companion object {
        private const val SAMPLE_PACKAGE = "test.samples"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "reflective-field-rule"
        private const val PRIMITIVE_TAINT_MARK = "tainted" + PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE
        private const val PRIMITIVE_RULE_ID = "reflective-primitive-field-rule"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private fun primitiveConfig(testCls: String) = SerializedTaintConfig(
        source = listOf(sourceRule(testCls, "intSource", PRIMITIVE_TAINT_MARK)),
        sink = listOf(
            sinkRule(testCls, "intSink", PRIMITIVE_RULE_ID, listOf(Argument(0) to PRIMITIVE_TAINT_MARK))
        )
    )

    private fun config(testCls: String) = SerializedTaintConfig(
        source = listOf(sourceRule(testCls, "source", TAINT_MARK)),
        sink = listOf(sinkRule(testCls, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    @Test
    fun `control - a direct field write and read reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveFieldSample"
        assertReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "directFieldFlow",
            ruleId = RULE_ID,
            testName = "direct field"
        )
    }

    @Test
    fun `a reflective write and read of the same field reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveFieldSample"
        assertReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveSameFieldFlow",
            ruleId = RULE_ID,
            testName = "reflective same field"
        )
    }

    @Test
    fun `a primitive reflective write and read of the same field reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveFieldSample"
        assertReachable(
            config = primitiveConfig(testCls),
            testCls = testCls,
            entryPointName = "reflectiveIntSameFieldFlow",
            ruleId = PRIMITIVE_RULE_ID,
            testName = "reflective same primitive field"
        )
    }

    @Test
    fun `a primitive reflective read of a different field does not reach the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveFieldSample"
        assertNotReachable(
            config = primitiveConfig(testCls),
            testCls = testCls,
            entryPointName = "reflectiveIntOtherFieldFlow",
            testName = "reflective other primitive field"
        )
    }

    @Test
    fun `a reflective read of a different field does not reach the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveFieldSample"
        assertNotReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveOtherFieldFlow",
            testName = "reflective other field"
        )
    }
}
