package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetOutcomeTally
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.assertMarkSetDebugChecks
import org.opentaint.common.sast.dataflow.checkLogLine
import org.opentaint.common.sast.dataflow.runMarkSetPhase
import org.opentaint.common.sast.dataflow.violationLogLines
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.markset.CoverageViolation
import org.opentaint.dataflow.ap.ifds.markset.MarkSetCoverage
import org.opentaint.dataflow.ap.ifds.markset.MethodCfgSource
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
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
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
            allowedFailOpen = setOf("recorder cap"),
        )

        assertEquals(MarkSetOutcome.FailOpen("recorder cap"), lastMarkSetOutcome)
        assertEquals(findings(baseline), findings(capped))
    }

    @Test
    fun `a recorder byte cap fails open and keeps the findings`() {
        val baseline = runAnalysis(simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"))
        val capped = runAnalysis(
            simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"),
            markSet = enabled.copy(maxRecorderBytes = 1),
            allowedFailOpen = setOf("recorder cap"),
        )

        assertEquals(MarkSetOutcome.FailOpen("recorder cap"), lastMarkSetOutcome)
        assertEquals(findings(baseline), findings(capped))
    }

    @Test
    fun `the debug-check log reports the counts per check and caps the violation lines`() {
        val violations = List(3) { CoverageViolation("E1", "call $it") } + CoverageViolation("E2", "site")
        val coverage = MarkSetCoverage(violations, observedCalls = 7, observedSites = 9, uncoveredSites = 2)

        assertEquals(
            "markset-check: e1=3 e2=1 e10=n/a violations=4 calls=7 sites=9 uncoveredSites=2",
            coverage.checkLogLine(),
        )
        assertEquals(
            listOf("markset-check E1: call 0", "markset-check E1: call 1", "markset-check: 2 more violations"),
            coverage.violationLogLines(limit = 2),
        )
        assertEquals(
            "markset-check: e1=0 e2=0 e10=n/a violations=0 calls=0 sites=0 uncoveredSites=0",
            MarkSetCoverage(emptyList(), 0, 0, 0).checkLogLine(),
        )
    }

    @Test
    fun `a differential pair whose mark-set run failed open fails unless the reason is allowed`() {
        val failOpen = MarkSetOutcome.FailOpen("time limit")

        assertFailsWith<AssertionError> { assertMarkSetDebugChecks(emptySet(), emptySet(), failOpen, null, "pair") }
        assertFailsWith<AssertionError> { assertMarkSetDebugChecks(emptySet(), emptySet(), null, null, "pair") }
        assertMarkSetDebugChecks(emptySet(), emptySet(), failOpen, null, "pair", allowedFailOpen = setOf("time limit"))

        val tally = MarkSetOutcomeTally()
        tally.record(failOpen)
        tally.record(MarkSetOutcome.FailOpen("recorder cap"))
        tally.record(failOpen)
        assertEquals("markset-diff Suite: selected=0 failOpen=3 {recorder cap=1, time limit=2}", tally.summary("Suite"))
    }

    /** Throws from every prescan runner's first event, and delegates otherwise (the M7 test). */
    private class FailingPrescan(private val base: TaintAnalysisManager) : TaintAnalysisManager by base {
        @Volatile
        private var phase: TaintAnalysisManager.Phase = TaintAnalysisManager.Phase.Prescan

        override fun selectPhase(phase: TaintAnalysisManager.Phase) {
            this.phase = phase
            base.selectPhase(phase)
        }

        override fun getMethodEntrypointResolver(
            graph: ApplicationGraph<CommonMethod, CommonInst>,
        ): MethodEntrypointResolver {
            check(phase !is TaintAnalysisManager.Phase.Prescan) { "injected prescan failure" }
            return base.getMethodEntrypointResolver(graph)
        }
    }

    @Test
    fun `a runner exception in the prescan leaves a non-OK status and fails open`() {
        // The same failure with the flag off: the full scan keeps only the rules the failed prescan
        // saw, so it is the baseline a fail-open run must match.
        val baseline = runAnalysisOnce(
            simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"), MarkSetScanOptions(), wrapManager = ::FailingPrescan,
        )
        val failed = runAnalysisOnce(
            simpleConfig, SIMPLE_CLS, listOf("simpleDataFlow"), enabled, wrapManager = ::FailingPrescan,
        )

        // Read by the mark-set phase, right after the prescan's `runAnalysis` returned (spec §10, M7).
        assertEquals(TaintAnalysisUnitRunnerManager.Status.EXCEPTION, failed.statusAfterPrescan)
        assertEquals(MarkSetOutcome.FailOpen("prescan incomplete"), failed.markSetOutcome)
        assertEquals(findings(baseline.findings), findings(failed.findings))
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
    private fun recordedProgram(recordCalls: Boolean = false): Triple<MarkSetRecorder, JIRMethod, List<JIRInst>> {
        val method = sampleMethod(SIMPLE_CLS, "simpleDataFlow")
        val statements = method.instList.take(3)
        val field = cp.findClassOrNull("test.samples.StaticFieldSample")!!.declaredFields.single { it.name == "staticField" }

        val recorder = MarkSetRecorder(recordCalls = recordCalls)
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

    /** A straight-line statement graph over the method's instruction list, indexed by location. */
    private val straightLineCfg = object : MethodCfgSource {
        override fun indexOf(statement: CommonInst): Int = (statement as JIRInst).location.index

        override fun graphOf(method: CommonMethod): MethodCfgSource.MethodGraph {
            val count = (method as JIRMethod).instList.size
            return MethodCfgSource.MethodGraph(
                stmtCount = count,
                succ = Array(count) { if (it + 1 < count) intArrayOf(it + 1) else IntArray(0) },
                entries = intArrayOf(0),
                exits = intArrayOf(count - 1),
            )
        }
    }

    private val flowSensitive = enabled.copy(flowSensitive = true)

    @Test
    fun `option 3* selects like the default mode on a straight-line program`() {
        val (recorder, method, statements) = recordedProgram(recordCalls = true)
        val outcome = assertIs<MarkSetOutcome.Selected>(
            runMarkSetPhase(recorder, listOf(method), prescanOk = true, storeSummaries = false, flowSensitive, cfgSource = straightLineCfg)
        )
        // The source at statement 0 precedes the sink at statement 2.
        assertEquals(setOf(statements[0], statements[2]), outcome.rules.keys)
        assertEquals(1, outcome.selectedActions)
        assertTrue(outcome.stats.rootPoints > 0, "the flow-sensitive scan did not run")
        assertTrue(outcome.logLine().contains("rootPoints="), outcome.logLine())
    }

    @Test
    fun `option 3* without a statement graph or call points fails open`() {
        val withoutCfg = recordedProgram(recordCalls = true)
        assertEquals(
            MarkSetOutcome.FailOpen("flow-sensitive cfg"),
            runMarkSetPhase(withoutCfg.first, listOf(withoutCfg.second), prescanOk = true, storeSummaries = false, flowSensitive),
        )
        val withoutCalls = recordedProgram(recordCalls = false)
        assertEquals(
            MarkSetOutcome.FailOpen("flow-sensitive cfg"),
            runMarkSetPhase(
                withoutCalls.first, listOf(withoutCalls.second), prescanOk = true, storeSummaries = false, flowSensitive,
                cfgSource = straightLineCfg,
            ),
        )
    }

    @Test
    fun `option 3* over the size guard fails open`() {
        val (recorder, method, _) = recordedProgram(recordCalls = true)
        val outcome = runMarkSetPhase(
            recorder, listOf(method), prescanOk = true, storeSummaries = false, flowSensitive,
            cfgSource = straightLineCfg, maxRootPoints = 1,
        )
        assertEquals(MarkSetOutcome.FailOpen("flow-sensitive size"), outcome)
        assertTrue(!recorder.active)
        assertEquals(0, recorder.seal(listOf(method)).program.sites.size, "the recorder was not released")
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
