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
class ShallowScanRecallTest : AnalysisTest() {
    companion object {
        private const val TAINT_MARK = "tainted"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true
    override val useDefaultConfig: Boolean = true

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, checkNotNull(context.springWebProjectContext))

    private fun probe(
        sampleClass: String,
        entryPoints: List<Pair<String, Int>>,
        ruleId: String,
        shallowApMode: ApMode,
    ): Set<String> {
        val config = SerializedTaintConfig(
            entryPoint = entryPoints.map { (m, idx) -> entryPointRule(sampleClass, m, TAINT_MARK, argIndex = idx) },
            sink = listOf(sinkRule(sampleClass, "sink", ruleId, listOf(Argument(0) to TAINT_MARK))),
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

    private fun assertShallowModesAgree(name: String, sampleClass: String, entryPoints: List<Pair<String, Int>>) {
        val ruleId = "diag-$name"
        val tree = probe(sampleClass, entryPoints, ruleId, ApMode.Tree)
        val baseOnlyField = probe(sampleClass, entryPoints, ruleId, ApMode.BaseOnlyField)
        assertEquals(setOf(ruleId), tree, "$name: shallow=Tree lost the flow")
        assertEquals(tree, baseOnlyField, "$name: shallow=BaseOnlyField lost the flow that shallow=Tree finds")
    }

    @Test
    fun `taint stored into a spring bean field survives the shallow scan`() {
        val cls = "test.samples.SpringCrossEntryPointSample"
        assertShallowModesAgree("A-plain-same", cls, listOf("uploadAndDeletePlainField" to 0))
    }

    @Test
    fun `taint stored into a spring repository survives the shallow scan across entry points`() {
        val cls = "test.samples.SpringCrossEntryPointSample"
        assertShallowModesAgree("A-repo-cross", cls, listOf("uploadNewPlugin" to 0))
    }

    @Test
    fun `taint on a static field survives a dispatch made one frame below the write`() {
        val cls = "test.samples.ThreadStaticFieldSample"
        assertShallowModesAgree("C-helper", cls, listOf("exportViaHelper" to 0))
    }

    @Test
    fun `taint on a static field survives Thread start`() {
        val cls = "test.samples.ThreadStaticFieldSample"
        assertShallowModesAgree("C-subclass", cls, listOf("exportViaThreadSubclass" to 0))
    }

    @Test
    fun `taint on a static field survives a dispatch made in the writing frame`() {
        val cls = "test.samples.ThreadStaticFieldSample"
        assertShallowModesAgree("C-iface", cls, listOf("exportViaInterface" to 0))
    }

    @Test
    fun `whole object seed reaches a sink through a collection element getter`() {
        val cls = "test.samples.CollectionElementGetterSample"
        assertShallowModesAgree("B-list", cls, listOf("searchViaList" to 0))
    }

    @Test
    fun `whole object seed reaches a sink through the shopizer getter chain`() {
        val cls = "test.samples.CollectionElementGetterSample"
        assertShallowModesAgree("B-shopizer", cls, listOf("searchShopizerShape" to 1))
    }
}
