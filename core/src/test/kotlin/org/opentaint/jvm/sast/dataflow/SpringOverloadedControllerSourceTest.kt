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
class SpringOverloadedControllerSourceTest : AnalysisTest() {
    companion object {
        private const val SAMPLE_CLASS = "test.samples.SpringOverloadedControllerSourceSample"
        private const val TAINT_MARK = "tainted"
        private const val FIRST_RULE_ID = "spring-overload-first"
        private const val SECOND_RULE_ID = "spring-overload-second"
    }

    override val sourceFileExtension: String = "java"

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    @Test
    fun `all overloaded Spring controller methods are seeded during shallow analysis`() {
        val generatedWrapperClass = findClass("${SAMPLE_CLASS}_Opentaint_EntryPoint")
        val overloadWrappers = generatedWrapperClass.declaredMethods.filter { it.name.startsWith("list") }
        assertEquals(2, overloadWrappers.mapTo(hashSetOf()) { it.name }.size)

        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(SAMPLE_CLASS, "list", TAINT_MARK, argIndex = 0)),
            sink = listOf(
                sinkRule(SAMPLE_CLASS, "sinkFirst", FIRST_RULE_ID, listOf(Argument(0) to TAINT_MARK)),
                sinkRule(SAMPLE_CLASS, "sinkSecond", SECOND_RULE_ID, listOf(Argument(0) to TAINT_MARK)),
            ),
        )

        val traces = runAnalysis(
            config = config,
            entryPointClass = GeneratedSpringControllerDispatcher,
            entryPointMethod = GeneratedSpringControllerDispatcherDispatchMethod,
            apMode = ApMode.BaseOnly,
        )

        assertEquals(setOf(FIRST_RULE_ID, SECOND_RULE_ID), traces.mapTo(hashSetOf()) { it.vulnerability.rule.id })
    }
}
