package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.runMarkSetPhase
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue
import kotlin.time.Duration

/**
 * Task 6: the mark-set phase runs between the prescan and the full scan (spec §10), installs
 * its selection, and fails open (spec §6.6) when its inputs cannot be trusted.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class MarkSetPhaseTest : AnalysisTest() {
    private companion object {
        const val SIMPLE_CLS = "test.samples.SimpleDataFlowSample"
        const val TAINT_MARK = "tainted"
        const val UNRELATED_MARK = "unrelated"
        const val RULE_ID = "simple-flow-rule"
        const val UNRELATED_RULE_ID = "unrelated-rule"
    }

    override val sourceFileExtension: String = "java"

    private val simpleConfig = SerializedTaintConfig(
        source = listOf(sourceRule(SIMPLE_CLS, "source", TAINT_MARK)),
        sink = listOf(sinkRule(SIMPLE_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK))),
    )

    private val enabled = MarkSetScanOptions(enabled = true)

    private fun findings(result: List<VulnerabilityWithTrace>) =
        result.mapTo(hashSetOf()) { it.vulnerability.rule.id to it.vulnerability.statement }

    @Test
    fun `the flag on gives the same findings as off and a selection`() {
        val baseline = runAnalysis(simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"))
        assertEquals(null, lastMarkSetOutcome, "the mark-set phase ran with the flag off")

        val markSet = runAnalysis(simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"), markSet = enabled)
        val outcome = assertIs<MarkSetOutcome.Selected>(lastMarkSetOutcome)

        assertTrue(baseline.isNotEmpty(), "baseline found nothing")
        assertEquals(findings(baseline), findings(markSet))
        assertTrue(outcome.rules.isNotEmpty(), "the selection is empty")
    }

    @Test
    fun `an unrelated rule whose sink never fires has no selected source`() {
        val config = SerializedTaintConfig(
            source = listOf(
                sourceRule(SIMPLE_CLS, "source", TAINT_MARK),
                sourceRule(SIMPLE_CLS, "process", UNRELATED_MARK),
            ),
            sink = listOf(
                sinkRule(SIMPLE_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)),
                sinkRule(SIMPLE_CLS, "sink", UNRELATED_RULE_ID, listOf(Argument(0) to "never-produced")),
            ),
        )

        val baseline = runAnalysis(config, SIMPLE_CLS, listOf("simpleDataFlow"))
        val markSet = runAnalysis(config, SIMPLE_CLS, listOf("simpleDataFlow"), markSet = enabled)
        assertEquals(findings(baseline), findings(markSet))

        val outcome = assertIs<MarkSetOutcome.Selected>(lastMarkSetOutcome)
        val selectedSources = outcome.rules.entries.flatMap { (statement, rules) ->
            rules.entries
                .filter { it.key is TaintMethodSource }
                .map { (statement as JIRInst).callExpr?.method?.name to it.value }
        }

        assertTrue(selectedSources.none { it.first == "process" }, "the unrelated source is selected: $selectedSources")
        val sourceActions = selectedSources.filter { it.first == "source" }.flatMap { it.second }
        assertEquals(listOf(TAINT_MARK), sourceActions.map { (it as AssignMark).mark.name })

        val processCalls = outcome.covered.filter { (it as JIRInst).callExpr?.method?.name == "process" }
        assertTrue(processCalls.isNotEmpty(), "the process call is not a covered statement")
    }

    @Test
    fun `an incomplete prescan fails open`() {
        val outcome = runMarkSetPhase(MarkSetRecorder(), emptyList(), prescanOk = false, storeSummaries = false, enabled)
        assertEquals(MarkSetOutcome.FailOpen("prescan incomplete"), outcome)
    }

    @Test
    fun `stored summaries fail open`() {
        val outcome = runMarkSetPhase(MarkSetRecorder(), emptyList(), prescanOk = true, storeSummaries = true, enabled)
        assertEquals(MarkSetOutcome.FailOpen("stored summaries"), outcome)
    }

    @Test
    fun `an exceeded time limit fails open`() {
        val outcome = runMarkSetPhase(
            MarkSetRecorder(), emptyList(), prescanOk = true, storeSummaries = false,
            enabled.copy(timeLimit = Duration.ZERO),
        )
        assertEquals(MarkSetOutcome.FailOpen("time limit"), outcome)
    }

    @Test
    fun `a recorder cap of one fails open and keeps the findings`() {
        val baseline = runAnalysis(simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"))
        val capped = runAnalysis(
            simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"),
            markSet = enabled.copy(maxSites = 1, maxEdges = 1),
        )

        assertEquals(MarkSetOutcome.FailOpen("recorder cap"), lastMarkSetOutcome)
        assertEquals(findings(baseline), findings(capped))
    }
}
