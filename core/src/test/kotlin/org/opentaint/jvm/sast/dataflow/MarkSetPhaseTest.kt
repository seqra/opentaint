package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.runMarkSetPhase
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.markset.SiteKind
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.jvm.Result
import org.opentaint.dataflow.configuration.jvm.TaintMark
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.jvm.JIRMethod
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

    private fun sampleMethod(cls: String, name: String): JIRMethod =
        cp.findClassOrNull(cls)!!.declaredMethods.single { it.name == name }

    private fun mark(name: String) = AssignMark(TaintMark(name), Result)

    private fun markLiteral(name: String) = RuleConditionRewriter.ExprOrConstant(
        TaintMarkAwareConditionExpr.ContainsMarkLiteral(
            PositionAccess.Simple(AccessPathBase.Argument(0)), TaintMarkAccessor(name), negated = false
        )
    )

    /**
     * One method holding: a method source recorded with two residuals (one `(statement, rule)`
     * pair, actions A, A, U; the second residual needs X), a static-field source, and a sink on A.
     * U is never needed.
     */
    private fun recordedProgram(): Triple<MarkSetRecorder, JIRMethod, List<JIRInst>> {
        val method = sampleMethod(SIMPLE_CLS, "simpleDataFlow")
        val statements = method.instList.take(3)
        val field = cp.findClassOrNull("test.samples.StaticFieldSample")!!.declaredFields.single { it.name == "staticField" }

        val recorder = MarkSetRecorder()
        recorder.active = true
        val source = TaintMethodSource(method, mkTrue(), listOf(mark("A"), mark("A"), mark("U")), info = null)
        recorder.recordSite(statements[0], source, SiteKind.SOURCE, RuleConditionRewriter.trueExpr, listOf("A", "A", "U"))
        recorder.recordSite(statements[0], source, SiteKind.SOURCE, markLiteral("X"), listOf("A", "A", "U"))
        val staticSource = TaintStaticFieldSource(field, mkTrue(), listOf(mark("A")), info = null)
        recorder.recordSite(statements[1], staticSource, SiteKind.SOURCE, RuleConditionRewriter.trueExpr, listOf("A"))
        val sink = TaintMethodSink(
            method, mkTrue(), emptyList(), "sink", TaintSinkMeta("sink", CommonTaintConfigurationSinkMeta.Severity.Error, null), info = null
        )
        recorder.recordSite(statements[2], sink, SiteKind.SINK, markLiteral("A"), emptyList())
        statements.forEach { recorder.recordStatement(it) }
        return Triple(recorder, method, statements)
    }

    @Test
    fun `the selection and its counts leave out static-field sources and count unique pairs`() {
        val (recorder, method, statements) = recordedProgram()
        val outcome = assertIs<MarkSetOutcome.Selected>(
            runMarkSetPhase(recorder, listOf(method), prescanOk = true, storeSummaries = false, enabled)
        )

        assertEquals(setOf(statements[0], statements[2]), outcome.rules.keys)
        assertEquals(listOf(mark("A")), outcome.rules.getValue(statements[0]).values.single().toList())
        assertEquals(emptySet(), outcome.rules.getValue(statements[2]).values.single())

        assertEquals(1, outcome.selectedActions)
        assertEquals(2, outcome.baselineActions)
        assertEquals(1, outcome.selectedSourceRules)
        assertEquals(1, outcome.baselineSourceRules)
        assertEquals(1, outcome.selectedSinks)
        assertEquals(1, outcome.baselineSinks)
        assertTrue(
            outcome.logLine().contains("selectedActions=1/baselineActions=2 selectedSinks=1/baselineSinks=1 sourceRules=1/1"),
            outcome.logLine(),
        )
    }

    @Test
    fun `the phase releases the recorder on every path`() {
        val paths = listOf<(MarkSetRecorder, JIRMethod) -> MarkSetOutcome>(
            { r, m -> runMarkSetPhase(r, listOf(m), prescanOk = true, storeSummaries = false, enabled) },
            { r, m -> runMarkSetPhase(r, listOf(m), prescanOk = false, storeSummaries = false, enabled) },
            { r, m -> runMarkSetPhase(r, listOf(m), prescanOk = true, storeSummaries = true, enabled) },
            { r, m -> r.overflow = true; runMarkSetPhase(r, listOf(m), prescanOk = true, storeSummaries = false, enabled) },
            { r, m ->
                runMarkSetPhase(r, listOf(m), prescanOk = true, storeSummaries = false, enabled.copy(timeLimit = Duration.ZERO))
            },
        )
        for (path in paths) {
            val (recorder, method, _) = recordedProgram()
            val outcome = path(recorder, method)
            val left = recorder.seal(listOf(method))
            assertEquals(0, left.program.sites.size, "sites left after $outcome")
            assertEquals(0, left.program.methodCount, "methods left after $outcome")
            assertTrue(left.coveredStatements.isEmpty(), "covered statements left after $outcome")
            assertTrue(!recorder.active)
        }
    }
}
