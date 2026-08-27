package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

class PrescanInitializationTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"
    override val wholeClassPrescan: Boolean = true

    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(TEST_CLASS, "source", MARK)),
        sink = listOf(sinkRule(TEST_CLASS, "sink", RULE_ID, listOf(Argument(0) to MARK))),
    )

    @Test
    fun `class initializer callable is available to unrelated static method`() {
        assertReachable(
            config,
            TEST_CLASS,
            "staticEntry",
            RULE_ID,
            "static initializer propagation",
        )
    }

    @Test
    fun `constructor callable is available to instance method of same class`() {
        assertReachable(
            config,
            TEST_CLASS,
            "instanceEntry",
            RULE_ID,
            "constructor receiver propagation",
        )
    }

    @Test
    fun `unreachable private prescan root does not become a full scan root`() {
        assertNotReachable(
            config,
            TEST_CLASS,
            "safeEntry",
            "prescan and full-scan root isolation",
        )
    }

    companion object {
        private const val TEST_CLASS = "test.samples.PrescanInitializationSample"
        private const val MARK = "prescan-init"
        private const val RULE_ID = "prescan-init-sink"

    }
}
