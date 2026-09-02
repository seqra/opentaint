package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class KotlinReflectiveFieldAnalysisTest : AnalysisTest() {

    companion object {
        private const val SAMPLE_CLASS = "test.samples.KotlinReflectiveFieldSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "kt-reflective-field-rule"
    }

    override val sourceFileExtension: String = "kt"
    override val useDefaultConfig: Boolean = true

    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(SAMPLE_CLASS, "source", TAINT_MARK)),
        sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    @Test
    fun `a reflective write and read of the same field reaches the sink`() {
        assertReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "reflectiveSameFieldFlow",
            ruleId = RULE_ID,
            testName = "kotlin reflective same field"
        )
    }

    @Test
    fun `the bench fixture shape - object, extra clean write - does not reach the sink`() {
        val benchCls = "test.samples.KotlinReflectiveFieldBenchSample"
        assertNotReachable(
            config = SerializedTaintConfig(
                source = listOf(sourceRule(benchCls, "source", TAINT_MARK)),
                sink = listOf(sinkRule(benchCls, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
            ),
            testCls = benchCls,
            entryPointName = "run",
            testName = "kotlin bench-shaped computed property"
        )
    }

    @Test
    fun `bisect - class plus the extra clean write`() {
        assertNotReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "classWithExtraCleanWriteFlow",
            testName = "class + extra clean write"
        )
    }

    @Test
    fun `bisect - object without the extra clean write`() {
        val benchCls = "test.samples.KotlinReflectiveFieldBenchSample"
        assertNotReachable(
            config = SerializedTaintConfig(
                source = listOf(sourceRule(benchCls, "source", TAINT_MARK)),
                sink = listOf(sinkRule(benchCls, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
            ),
            testCls = benchCls,
            entryPointName = "objectWithoutExtraCleanWriteFlow",
            testName = "object without extra clean write"
        )
    }

    @Test
    fun `a reflective read of a different field does not reach the sink`() {
        assertNotReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "reflectiveOtherFieldFlow",
            testName = "kotlin reflective other field"
        )
    }
}
