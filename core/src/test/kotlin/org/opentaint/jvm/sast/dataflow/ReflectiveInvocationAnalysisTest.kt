package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ReflectiveInvocationAnalysisTest : AnalysisTest() {

    companion object {
        private const val SAMPLE_PACKAGE = "test.samples"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "reflective-invocation-rule"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private fun config(testCls: String) = SerializedTaintConfig(
        source = listOf(sourceRule(testCls, "source", TAINT_MARK)),
        sink = listOf(sinkRule(testCls, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    @Test
    fun `control - a direct call to the target reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        assertReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "directInvocationFlow",
            ruleId = RULE_ID,
            testName = "direct invocation"
        )
    }

    @Test
    fun `getMethod with a constant name resolves to the leaking target`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        assertReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveLeakFlow",
            ruleId = RULE_ID,
            testName = "reflective leak"
        )
    }

    @Test
    fun `getDeclaredMethod with an inline constant name resolves to the leaking target`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        assertReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveDeclaredLeakFlow",
            ruleId = RULE_ID,
            testName = "reflective declared leak"
        )
    }

    @Test
    fun `a primitive argument passed through invoke reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        val primitiveMark = "tainted" + PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE
        val primitiveConfig = SerializedTaintConfig(
            source = listOf(sourceRule(testCls, "intSource", primitiveMark)),
            sink = listOf(sinkRule(testCls, "intSink", "reflective-int-rule", listOf(Argument(0) to primitiveMark)))
        )
        assertReachable(
            config = primitiveConfig,
            testCls = testCls,
            entryPointName = "reflectiveIntLeakFlow",
            ruleId = "reflective-int-rule",
            testName = "reflective int leak"
        )
    }

    @Test
    fun `a constant name selecting a dropping target does not reach the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        assertNotReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveDropFlow",
            testName = "reflective drop"
        )
    }

    @Test
    fun `an ambiguous name dispatches to every candidate and reaches the sink`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        assertReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveAmbiguousFlow",
            ruleId = RULE_ID,
            testName = "reflective ambiguous"
        )
    }

    @Test
    fun `an unresolvable name is reported as a resolution failure and is not redirected`() {
        val testCls = "$SAMPLE_PACKAGE.ReflectiveInvocationSample"
        assertNotReachable(
            config = config(testCls),
            testCls = testCls,
            entryPointName = "reflectiveUnresolvedFlow",
            testName = "reflective unresolved"
        )
    }
}
