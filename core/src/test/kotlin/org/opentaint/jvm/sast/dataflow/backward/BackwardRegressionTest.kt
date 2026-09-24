package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFieldRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTypeNameMatcher

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BackwardRegressionTest : BackwardAnalysisTest() {
    companion object {
        private const val SAMPLE_PACKAGE = "test.samples"
        private const val SAMPLE_CLASS = "BackwardRegressionSample"
        private const val CLS = "$SAMPLE_PACKAGE.$SAMPLE_CLASS"
        private const val MARK = "tainted"
        private const val SINK_RULE = "backward-regression-sink"
    }

    override val sourceFileExtension: String = "java"
    override val useDefaultConfig: Boolean = true

    private fun entryConfig(entryMethod: String) = SerializedTaintConfig(
        entryPoint = listOf(entryPointRule(CLS, entryMethod, MARK, argIndex = 0)),
        sink = listOf(sinkRule(CLS, "sink", SINK_RULE, listOf(Argument(0) to MARK))),
    )

    private fun assertBothDirections(root: String, expected: Boolean, entryMethod: String = root) {
        val config = entryConfig(entryMethod)

        val forward = runAnalysis(config, CLS, root).any { it.vulnerability.rule.id == SINK_RULE }
        assertEquals(expected, forward, "$root: forward reference")

        val backward = runBackwardAnalysis(config, CLS, root)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, backward.status, "$root: backward status")
        val reached = backward.sourceFindings.any { finding ->
            val rule = finding.rule
            finding.mark == TaintMarkAccessor(MARK) && rule is TaintEntryPointSource && rule.method.name == entryMethod
        }
        assertEquals(expected, reached, "$root: backward, findings ${backward.sourceFindings}")
    }

    @Test
    fun `sink on a branch that ends in a throw`() = assertBothDirections("throwingBranch", expected = true)

    @Test
    fun `sink inside a callee that always throws`() = assertBothDirections("callsFailing", expected = true)

    @Test
    fun `sink in a catch handler that rethrows`() = assertBothDirections("catchThenRethrow", expected = true)

    @Test
    fun `heap effect of a callee that always throws does not reach the caller`() =
        assertBothDirections("callsTaintThenThrow", expected = false, entryMethod = "callsTaintThenThrow")

    @Test
    fun `sink in a loop without exit`() = assertBothDirections("infiniteLoop", expected = false)

    @Test
    fun `call-site alias rooted at an argument`() = assertBothDirections("aliasOnArgumentPath", expected = true)

    @Test
    fun `call-site alias rooted at this`() = assertBothDirections("aliasOnThisPath", expected = true)

    @Test
    fun `call-site alias rooted at a local`() = assertBothDirections("aliasOnLocalPath", expected = true)

    @Test
    fun `call-site alias rooted at a static field`() = assertBothDirections("aliasOnStaticPath", expected = true)

    @Test
    fun `entry source of a callee does not taint the caller argument`() =
        assertBothDirections("callsEntryHandler", expected = false, entryMethod = "entryHandler")

    @Test
    fun `entry source of a callee reaches the caller through a field of an argument`() =
        assertBothDirections("callsEntryHandlerStoring", expected = true, entryMethod = "entryHandlerStores")

    @Test
    fun `entry source of a callee reaches the caller through the return value`() =
        assertBothDirections("callsEntryHandlerReturning", expected = true, entryMethod = "entryHandlerReturns")

    @Test
    fun `entry source of a callee reaches a sink inside the callee`() =
        assertBothDirections("callsEntryHandlerSinking", expected = true, entryMethod = "entryHandlerSinks")

    @Test
    fun `entry source of a callee reaches the caller through a static field`() =
        assertBothDirections("callsEntryHandlerPublishing", expected = true, entryMethod = "entryHandlerPublishes")

    private fun sink() = sinkRule(CLS, "sink", SINK_RULE, listOf(Argument(0) to MARK))
        .copy(serializedId = SINK_RULE)

    private fun assertStagedSourceReached(config: SerializedTaintConfig, root: String, isExpectedSource: (Any) -> Boolean) {
        val result = runBackwardAnalysis(config, CLS, root, stagedRuleSelection = true)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "$root: backward status")
        assertTrue(
            result.sourceFindings.any { it.mark == TaintMarkAccessor(MARK) && isExpectedSource(it.rule) },
            "$root: the source rule must survive the prescan rule selection, got ${result.sourceFindings}"
        )
    }

    @Test
    fun `prescan selects call source rules`() {
        val config = SerializedTaintConfig(
            source = listOf(sourceRule(CLS, "source", MARK).copy(serializedId = "call-source")),
            sink = listOf(sink()),
        )
        assertStagedSourceReached(config, "callSourceFlow") { it is TaintMethodSource && it.serializedId == "call-source" }
    }

    @Test
    fun `prescan selects entry point source rules`() {
        val config = SerializedTaintConfig(
            entryPoint = listOf(entryPointRule(CLS, "entrySourceFlow", MARK, argIndex = 0).copy(serializedId = "entry-source")),
            sink = listOf(sink()),
        )
        assertStagedSourceReached(config, "entrySourceFlow") { it is TaintEntryPointSource && it.serializedId == "entry-source" }
    }

    private fun exitSourceConfig() = SerializedTaintConfig(
        methodExitSource = listOf(
            SerializedRule.MethodExitSource(
                function = functionMatcher(CLS, "exitSource"),
                taint = listOf(SerializedTaintAssignAction(kind = MARK, pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result))),
                serializedId = "exit-source",
            )
        ),
        sink = listOf(sink()),
    )

    @Test
    fun `exit source of a callee returning a constant`() {
        val config = exitSourceConfig()
        assertTrue(runAnalysis(config, CLS, "exitSourceFlow").isNotEmpty(), "exitSourceFlow: forward reference")
        val result = runBackwardAnalysis(config, CLS, "exitSourceFlow")
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "exitSourceFlow: backward status")
        assertTrue(
            result.sourceFindings.any { it.mark == TaintMarkAccessor(MARK) && it.rule is TaintMethodExitSource },
            "exitSourceFlow: the refined result demand must reach the exit source, got ${result.sourceFindings}"
        )
    }

    @Test
    fun `prescan selects method exit source rules`() {
        val config = exitSourceConfig()
        assertStagedSourceReached(config, "exitSourceFlow") { it is TaintMethodExitSource && it.serializedId == "exit-source" }
    }

    @Test
    fun `prescan selects static field source rules`() {
        val config = SerializedTaintConfig(
            staticFieldSource = listOf(
                SerializedFieldRule.SerializedStaticFieldSource(
                    className = SerializedTypeNameMatcher.ClassPattern(
                        `package` = SerializedSimpleNameMatcher.Simple(SAMPLE_PACKAGE),
                        `class` = SerializedSimpleNameMatcher.Simple(SAMPLE_CLASS),
                    ),
                    fieldName = SerializedSimpleNameMatcher.Simple("STATIC_SOURCE"),
                    condition = null,
                    taint = listOf(SerializedTaintAssignAction(kind = MARK, pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result))),
                    serializedId = "static-source",
                )
            ),
            sink = listOf(sink()),
        )
        assertStagedSourceReached(config, "staticSourceFlow") { it is TaintStaticFieldSource && it.serializedId == "static-source" }
    }
}
