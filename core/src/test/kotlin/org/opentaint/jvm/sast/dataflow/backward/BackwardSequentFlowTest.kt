package org.opentaint.jvm.sast.dataflow.backward

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFieldRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTypeNameMatcher

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BackwardSequentFlowTest : BackwardAnalysisTest() {
    companion object {
        private const val SAMPLE_PACKAGE = "test.samples"
        private const val SAMPLE_CLASS = "BackwardSequentSample"
        private const val CLS = "$SAMPLE_PACKAGE.$SAMPLE_CLASS"
        private const val MARK = "tainted"
        private const val PRIMITIVE_MARK = "tainted%%primitive%%"
        private const val SINK_RULE = "backward-sequent-sink"
        private const val EXIT_SINK_RULE = "backward-sequent-exit-sink"
    }

    override val sourceFileExtension: String = "java"

    private fun entryConfig(method: String, mark: String = MARK) = SerializedTaintConfig(
        entryPoint = listOf(entryPointRule(CLS, method, mark, argIndex = 0)),
        sink = listOf(
            sinkRule(CLS, "sink", SINK_RULE, listOf(Argument(0) to mark)),
            sinkRule(CLS, "sinkInt", SINK_RULE, listOf(Argument(0) to mark)),
        ),
    )

    private fun exitSinkConfig(method: String) = SerializedTaintConfig(
        entryPoint = listOf(entryPointRule(CLS, method, MARK, argIndex = 0)),
        methodExitSink = listOf(methodExitSinkRule(CLS, method, EXIT_SINK_RULE, MARK)),
    )

    private fun staticSourceConfig(field: String) = SerializedTaintConfig(
        sink = listOf(sinkRule(CLS, "sink", SINK_RULE, listOf(Argument(0) to MARK))),
        staticFieldSource = listOf(
            SerializedFieldRule.SerializedStaticFieldSource(
                className = SerializedTypeNameMatcher.ClassPattern(
                    `package` = SerializedSimpleNameMatcher.Simple(SAMPLE_PACKAGE),
                    `class` = SerializedSimpleNameMatcher.Simple(SAMPLE_CLASS),
                ),
                fieldName = SerializedSimpleNameMatcher.Simple(field),
                condition = null,
                taint = listOf(
                    SerializedTaintAssignAction(
                        kind = MARK,
                        pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                    )
                ),
            )
        ),
    )

    private fun run(config: SerializedTaintConfig, method: String): BackwardResult {
        val result = runBackwardAnalysis(config, CLS, method)
        assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, result.status, "$method: analysis status")
        assertTrue(result.demandSeeds.isNotEmpty(), "$method: sink demand must be seeded")
        return result
    }

    private fun BackwardResult.entrySourceFindings(method: String, mark: String) = sourceFindings.filter { finding ->
        val rule = finding.rule
        finding.mark == TaintMarkAccessor(mark) &&
            rule is TaintEntryPointSource && rule.method.name == method &&
            finding.statement.location.method.name == method
    }

    private fun assertEntryReached(
        method: String,
        mark: String = MARK,
        config: SerializedTaintConfig = entryConfig(method, mark),
    ) {
        val result = run(config, method)
        assertTrue(
            result.entrySourceFindings(method, mark).isNotEmpty(),
            "$method: expected the sink demand to reach the entry argument source, got ${result.sourceFindings}"
        )
    }

    private fun assertEntryNotReached(
        method: String,
        mark: String = MARK,
        config: SerializedTaintConfig = entryConfig(method, mark),
    ) {
        val result = run(config, method)
        assertTrue(
            result.sourceFindings.isEmpty(),
            "$method: expected no source to be reached, got ${result.sourceFindings}"
        )
    }

    @Test
    fun `simple assign chain`() = assertEntryReached("simpleAssign")

    @Test
    fun `simple assign from untainted argument`() = assertEntryNotReached("simpleAssignNegative")

    @Test
    fun `local overwrite kills the demand`() = assertEntryNotReached("overwriteLocal")

    @Test
    fun `cast propagates the demand`() = assertEntryReached("castFlow")

    @Test
    fun `field write then read`() = assertEntryReached("fieldWriteRead")

    @Test
    fun `field overwrite is a strong update`() = assertEntryNotReached("fieldOverwrite")

    @Test
    fun `other field is not demanded`() = assertEntryNotReached("otherField")

    @Test
    fun `write to other field keeps the demand`() = assertEntryReached("fieldKeepOther")

    @Test
    fun `field write through alias`() = assertEntryReached("fieldAlias")

    @Test
    fun `field write to a non aliased object`() = assertEntryNotReached("fieldNoAlias")

    @Test
    fun `array write through alias`() = assertEntryReached("arrayAlias")

    @Test
    fun `array write then read`() = assertEntryReached("arrayWriteRead")

    @Test
    fun `array write is a weak update`() = assertEntryReached("arrayWeakUpdate")

    @Test
    fun `array element never tainted`() = assertEntryNotReached("arrayNegative")

    @Test
    fun `static write then read`() = assertEntryReached("staticWriteRead")

    @Test
    fun `static overwrite is a strong update`() = assertEntryNotReached("staticOverwrite")

    @Test
    fun `static field source is matched at the static read`() {
        val method = "staticFieldSource"
        val result = run(staticSourceConfig("SOURCE_FIELD"), method)
        val findings = result.sourceFindings.filter {
            val rule = it.rule
            rule is TaintStaticFieldSource && rule.field.name == "SOURCE_FIELD" && it.mark == TaintMarkAccessor(MARK)
        }
        assertTrue(findings.isNotEmpty(), "$method: expected a static field source finding, got ${result.sourceFindings}")
        assertTrue(
            findings.all { it.statement.location.method.name == method },
            "$method: finding must be at the static read: $findings"
        )
    }

    @Test
    fun `static field source is not matched for other fields`() {
        val result = run(staticSourceConfig("SOURCE_FIELD"), "staticFieldSourceNegative")
        assertTrue(result.sourceFindings.isEmpty(), "unexpected findings: ${result.sourceFindings}")
    }

    @Test
    fun `binary expression left operand`() = assertEntryReached("binaryFlow", PRIMITIVE_MARK)

    @Test
    fun `binary expression right operand`() = assertEntryReached("binaryFlowRight", PRIMITIVE_MARK)

    @Test
    fun `binary expression on untainted operand`() = assertEntryNotReached("binaryNegative", PRIMITIVE_MARK)

    @Test
    fun `self referential read`() = assertEntryReached("selfRead")

    @Test
    fun `self referential read does not resurrect the killed local`() = assertEntryNotReached("selfReadNoResurrect")

    @Test
    fun `self referential write`() = assertEntryReached("selfWrite")

    @Test
    fun `self referential write replaces the old field value`() = assertEntryNotReached("selfWriteNegative")

    @Test
    fun `branch merge`() = assertEntryReached("branchFlow")

    @Test
    fun `loop carried flow`() = assertEntryReached("loopFlow")

    @Test
    fun `loop without tainted value`() = assertEntryNotReached("loopNegative")

    @Test
    fun `method exit sink demand reaches the entry`() =
        assertEntryReached("exitFlow", config = exitSinkConfig("exitFlow"))

    @Test
    fun `method exit sink demand on constant`() =
        assertEntryNotReached("exitNegative", config = exitSinkConfig("exitNegative"))
}
