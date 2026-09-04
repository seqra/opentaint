package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcher
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcherDispatchMethod
import org.opentaint.jvm.sast.project.spring.SpringRuleProvider

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BaseOnlyShallowReturnSinkTraceTest : AnalysisTest() {
    companion object {
        private const val SAMPLE_CLASS = "test.samples.SpringRepositoryReturnSinkSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "spring-repository-return-sink"
    }

    override val sourceFileExtension: String = "java"

    override val useDefaultUnrollStrategy: Boolean = true

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    private fun analyze(shallowApMode: ApMode): Set<String> {
        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(SAMPLE_CLASS, "update", TAINT_MARK, argIndex = 0)),
            methodExitSink = listOf(methodExitSinkRule(SAMPLE_CLASS, "render", RULE_ID, TAINT_MARK)),
        )

        val traces = runAnalysis(
            config = config,
            entryPointClass = GeneratedSpringControllerDispatcher,
            entryPointMethod = GeneratedSpringControllerDispatcherDispatchMethod,
            apMode = ApMode.Tree,
            shallowApMode = shallowApMode,
        )

        return traces.mapTo(hashSetOf()) { it.vulnerability.rule.id }
    }

    @Test
    fun `tree shallow scan resolves the method exit sink trace`() {
        assertEquals(setOf(RULE_ID), analyze(ApMode.Tree))
    }

    @Test
    fun `base only shallow scan resolves the method exit sink trace`() {
        assertEquals(setOf(RULE_ID), analyze(ApMode.BaseOnlyField))
    }
}
