package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class RepositoryFragmentCallResolutionTest : AnalysisTest() {

    companion object {
        private const val SAMPLE_CLASS = "test.samples.RepositoryFragmentSample"
        private const val LIBRARY_SAMPLE_CLASS = "test.samples.LibraryFragmentSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "repository-fragment-flow"
    }

    override val sourceFileExtension: String = "java"

    private val config = SerializedTaintConfig(
        entryPoint = listOf(entryPointRule(SAMPLE_CLASS, "listProducts", TAINT_MARK, argIndex = 0)),
        sink = listOf(sinkRule(SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
    )

    private val libraryConfig = SerializedTaintConfig(
        entryPoint = listOf(entryPointRule(LIBRARY_SAMPLE_CLASS, "listProducts", TAINT_MARK, argIndex = 0)),
        sink = listOf(sinkRule(LIBRARY_SAMPLE_CLASS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
    )

    @Test
    fun `fragment implementation is reachable through repository typed receiver with Tree`() {
        assertReachable(
            config = config,
            testCls = SAMPLE_CLASS,
            entryPointName = "listProducts",
            ruleId = RULE_ID,
            testName = "repository fragment (Tree)",
            apMode = ApMode.Tree,
        )
    }

    @Test
    fun `fragment declared outside the project is deliberately not widened`() {
        assertNotReachable(
            config = libraryConfig,
            testCls = LIBRARY_SAMPLE_CLASS,
            entryPointName = "listProducts",
            testName = "library fragment widening guard",
            apMode = ApMode.Tree,
        )
    }
}
