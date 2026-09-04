package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcher
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcherDispatchMethod
import org.opentaint.jvm.sast.project.spring.SpringRuleProvider

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SpringControllerReturnSinkTest : AnalysisTest() {
    companion object {
        private const val SAMPLE_CLASS = "test.samples.SpringControllerReturnSinkSample"
        private const val TAINT_MARK = "tainted"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true
    override val useDefaultConfig: Boolean = true

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    private fun assertSinkReached(method: String) {
        val ruleId = "spring-return-$method"
        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(SAMPLE_CLASS, method, TAINT_MARK, argIndex = 0)),
            methodExitSink = listOf(methodExitSinkRule(SAMPLE_CLASS, method, ruleId, TAINT_MARK)),
        )

        val traces = runAnalysis(
            config = config,
            entryPointClass = GeneratedSpringControllerDispatcher,
            entryPointMethod = GeneratedSpringControllerDispatcherDispatchMethod,
        )

        assertEquals(setOf(ruleId), traces.mapTo(hashSetOf()) { it.vulnerability.rule.id })
    }

    @Test
    fun `tainted argument returned directly reaches the method exit sink`() {
        assertSinkReached("returnDirect")
    }

    @Test
    fun `tainted bean read through a String getter reaches the method exit sink`() {
        assertSinkReached("returnStringGetter")
    }

}
