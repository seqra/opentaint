package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcher
import org.opentaint.jvm.sast.project.spring.GeneratedSpringControllerDispatcherDispatchMethod
import org.opentaint.jvm.sast.project.spring.SpringRuleProvider

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BaseOnlyShallowTraceResolutionTest : AnalysisTest() {
    companion object {
        private const val SAMPLE_CLASS = "test.samples.SpringRepositoryStaticFlowSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "spring-repository-static-flow"
    }

    override val sourceFileExtension: String = "java"

    override val useDefaultUnrollStrategy: Boolean = true

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    private fun analyze(shallowApMode: ApMode): Set<String> {
        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(SAMPLE_CLASS, "update", TAINT_MARK, argIndex = 0)),
            sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
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
    fun `tree shallow scan resolves the class-static repository trace`() {
        assertEquals(setOf(RULE_ID), analyze(ApMode.Tree))
    }

    @Test
    fun `base only shallow scan resolves the class-static repository trace`() {
        assertEquals(setOf(RULE_ID), analyze(ApMode.BaseOnlyField))
    }
}
