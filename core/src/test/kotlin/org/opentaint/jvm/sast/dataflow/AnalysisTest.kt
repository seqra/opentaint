package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkFactKey
import org.opentaint.common.sast.dataflow.MarkSetFindings
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetOutcomeTally
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.common.sast.dataflow.assertMarkSetDebugChecks
import org.opentaint.common.sast.dataflow.assertSameMarkSetFindings
import org.opentaint.common.sast.dataflow.markFactKeys
import org.opentaint.config.JavaDefaultConfigLoader
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.markset.MarkSetCoverage
import org.opentaint.dataflow.ap.ifds.markset.MarkSetInput
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFunctionNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.graph.JApplicationSingleExitGraph
import org.opentaint.jvm.sast.ast.BasicTestUtils
import org.opentaint.jvm.sast.dataflow.DataFlowApproximationLoader.isApproximation
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.util.analysis.ApplicationGraph
import kotlin.time.Duration.Companion.minutes

/** The system property that turns on the differential run of every analysis (spec §8 Layer 3). */
const val MARKSET_DIFF_PROPERTY = "opentaint.markset.diff"

/**
 * The system property (`-PmarksetFlowSensitive=true`) that makes the default mark-set run of the
 * differential switch, and of [MarkSetDifferentialTest], use option 3* (spec §9).
 */
const val MARKSET_FLOW_SENSITIVE_PROPERTY = "opentaint.markset.flowSensitive"

/**
 * The mark-set options a differential run uses when the caller did not ask for mark-set mode. The
 * debug checks are on (spec §8 Layer 2/3).
 */
val defaultDifferentialMarkSet: MarkSetScanOptions
    get() = MarkSetScanOptions(
        enabled = true,
        flowSensitive = System.getProperty(MARKSET_FLOW_SENSITIVE_PROPERTY) == "true",
        debugChecks = true,
    )

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class AnalysisTest : BasicTestUtils() {
    fun functionMatcher(fqn: String, methodName: String) = SerializedFunctionNameMatcher.Simple(
        `package` = SerializedSimpleNameMatcher.Simple(fqn.substringBeforeLast('.')),
        `class` = SerializedSimpleNameMatcher.Simple(fqn.substringAfterLast('.')),
        name = SerializedSimpleNameMatcher.Simple(methodName)
    )

    fun List<Pair<PositionBase, String>>.condition(): SerializedCondition =
        SerializedCondition.and(map {
            SerializedCondition.ContainsMark(it.second, PositionBaseWithModifiers.BaseOnly(it.first))
        })

    fun sourceRule(
        fqn: String,
        methodName: String,
        taintMark: String,
        condition: List<Pair<PositionBase, String>> = emptyList()
    ): SerializedRule.Source = SerializedRule.Source(
        function = functionMatcher(fqn, methodName),
        condition = condition.condition(),
        taint = listOf(
            SerializedTaintAssignAction(
                kind = taintMark,
                pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result)
            )
        )
    )

    fun entryPointRule(fqn: String, methodName: String, taintMark: String, argIndex: Int) =
        SerializedRule.EntryPoint(
            function = functionMatcher(fqn, methodName),
            taint = listOf(
                SerializedTaintAssignAction(
                    kind = taintMark,
                    pos = PositionBaseWithModifiers.BaseOnly(Argument(argIndex))
                )
            )
        )

    fun sinkRule(
        fqn: String,
        methodName: String,
        ruleId: String,
        condition: List<Pair<PositionBase, String>>
    ): SerializedRule.Sink {
        return SerializedRule.Sink(
            condition = condition.condition(),
            function = functionMatcher(fqn, methodName),
            id = ruleId,
            meta = SinkMetaData(note = "Sink message: $ruleId")
        )
    }

    fun methodExitSinkRule(
        fqn: String,
        methodName: String,
        ruleId: String,
        mark: String
    ): SerializedRule.MethodExitSink {
        return SerializedRule.MethodExitSink(
            condition = listOf(PositionBase.Result to mark).condition(),
            function = functionMatcher(fqn, methodName),
            id = ruleId
        )
    }

    open val useDefaultConfig = false

    open val apMode: ApMode = ApMode.Tree

    open val analysisUnrollStrategy: AnyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled

    /** The mark-set shallow scan options of every [runAnalysis] (spec §10); off by default. */
    open val markSet: MarkSetScanOptions = MarkSetScanOptions()

    /** The sealed mark-set input of the last [runAnalysis], or `null` if it was never sealed. */
    var lastMarkSetInput: MarkSetInput? = null
        private set

    /** The mark-set phase outcome of the last [runAnalysis], or `null` if the phase did not run. */
    var lastMarkSetOutcome: MarkSetOutcome? = null
        private set

    /** The differential switch (spec §8 Layer 3): `-PmarksetDiff=true` sets this system property. */
    private val markSetDiff: Boolean = System.getProperty(MARKSET_DIFF_PROPERTY) == "true"

    /** The mark-set outcomes of this class' differential pairs, logged once the class is done. */
    private val differentialOutcomes = MarkSetOutcomeTally()

    @AfterAll
    fun logMarkSetDifferentialSummary() {
        if (markSetDiff) println(differentialOutcomes.summary(this::class.simpleName ?: "AnalysisTest"))
    }

    private class SingleLocationUnit(val loc: RegisteredLocation) : JIRUnitResolver {
        override fun resolve(method: JIRMethod): UnitType {
            if (method.enclosingClass.declaration.location == loc || isApproximation(method)) {
                return SingletonUnit
            }

            return UnknownUnit
        }

        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != this.loc
    }

    private val defaultConfig by lazy {
        JavaDefaultConfigLoader.loadConfig()
    }

    fun runAnalysis(
        config: SerializedTaintConfig,
        entryPointClass: String,
        entryPointMethod: String
    ): List<VulnerabilityWithTrace> = runAnalysis(config, entryPointClass, listOf(entryPointMethod))

    /**
     * Runs the analysis with [markSet]. Under the differential switch (`-PmarksetDiff=true`, spec §8
     * Layer 3) it runs twice, the baseline and then the mark-set selection with the debug checks on,
     * asserts that both pass [assertMarkSetDebugChecks] and report the same findings, and returns
     * the baseline's. The mark-set run must select unless it fails open for a reason in
     * [allowedFailOpen] (a test that fails open on purpose). The mark-set run is the requested one
     * when [markSet] is enabled, else [defaultDifferentialMarkSet]. [lastMarkSetInput] and
     * [lastMarkSetOutcome] describe the requested run only.
     */
    fun runAnalysis(
        config: SerializedTaintConfig,
        entryPointClass: String,
        entryPointMethods: List<String>,
        markSet: MarkSetScanOptions = this.markSet,
        allowedFailOpen: Set<String> = emptySet(),
    ): List<VulnerabilityWithTrace> {
        if (!markSetDiff) return runAnalysisOnce(config, entryPointClass, entryPointMethods, markSet).publish()

        val markSetOptions = (if (markSet.enabled) markSet else defaultDifferentialMarkSet).copy(debugChecks = true)
        val baseline = runAnalysisOnce(config, entryPointClass, entryPointMethods, MarkSetScanOptions(), collectFacts = true)
        val restricted = runAnalysisOnce(config, entryPointClass, entryPointMethods, markSetOptions, collectFacts = true)
        val what = "$entryPointClass$entryPointMethods"
        differentialOutcomes.record(restricted.markSetOutcome)
        assertMarkSetDebugChecks(baseline, restricted, what, allowedFailOpen)
        assertSameMarkSetFindings(baseline.gated, restricted.gated, what)

        (if (markSet.enabled) restricted else baseline).publish()
        return baseline.findings
    }

    /**
     * One run: its reported findings, its confirmed findings before the trace filter (spec E9),
     * and its mark-set phase observations: the E1/E2 [coverage] (debug checks only), the
     * [markFacts] the E10 diff compares (with `collectFacts` only), and the engine status the
     * mark-set phase saw right after the prescan (`null` if the phase did not run).
     */
    class AnalysisRun(
        val findings: List<VulnerabilityWithTrace>,
        val confirmed: List<TaintSinkTracker.TaintVulnerability>,
        val markSetInput: MarkSetInput?,
        val markSetOutcome: MarkSetOutcome?,
        val coverage: MarkSetCoverage? = null,
        val markFacts: Set<MarkFactKey>? = null,
        val statusAfterPrescan: TaintAnalysisUnitRunnerManager.Status? = null,
    ) {
        /** The findings the differential gate compares. */
        val gated: MarkSetFindings get() = MarkSetFindings(confirmed, findings)
    }

    /**
     * The mark-set debug checks of a differential pair (spec §7, §8 Layers 2 and 3): the mark-set
     * run selected (or failed open for a reason in [allowedFailOpen]) and passed E1 and E2, and both
     * runs have the same facts of every needed mark per statement (E10). Both runs must have
     * collected their facts.
     */
    fun assertMarkSetDebugChecks(
        baseline: AnalysisRun,
        markSet: AnalysisRun,
        what: String,
        allowedFailOpen: Set<String> = emptySet(),
    ) = assertMarkSetDebugChecks(
        checkNotNull(baseline.markFacts) { "no baseline facts for $what" },
        checkNotNull(markSet.markFacts) { "no mark-set facts for $what" },
        markSet.markSetOutcome, markSet.coverage, what, allowedFailOpen,
    )

    private fun AnalysisRun.publish(): List<VulnerabilityWithTrace> {
        lastMarkSetInput = markSetInput
        lastMarkSetOutcome = markSetOutcome
        return findings
    }

    /**
     * Runs the analysis once with [markSet]; does not touch [lastMarkSetInput] / [lastMarkSetOutcome].
     * With [collectFacts], the run keeps the marked facts of every statement for the E10 diff.
     * [wrapManager] wraps the engine's analysis manager (a test hook, e.g. to inject a failure).
     */
    fun runAnalysisOnce(
        config: SerializedTaintConfig,
        entryPointClass: String,
        entryPointMethods: List<String>,
        markSet: MarkSetScanOptions,
        collectFacts: Boolean = false,
        wrapManager: (TaintAnalysisManager) -> TaintAnalysisManager = { it },
    ): AnalysisRun {
        val cls = cp.findClassOrNull(entryPointClass) ?: error("Class $entryPointClass not found in CP")
        val eps = entryPointMethods.map { entryPointMethod ->
            cls.declaredMethods.singleOrNull { it.name == entryPointMethod }
                ?: error("No $entryPointMethod method in $entryPointClass")
        }

        val taintConfig = TaintConfiguration(cp)
        taintConfig.loadConfig(config)

        if (useDefaultConfig) {
            val defaultPassRules = SerializedTaintConfig(passThrough = defaultConfig?.passThrough)
            taintConfig.loadConfig(defaultPassRules)
        }

        var rulesProvider: TaintRulesProvider = JIRTaintRulesProvider(taintConfig)
        rulesProvider = JIRMethodExitRuleProvider(rulesProvider)

        val usages = runBlocking { cp.usagesExt() }
        val mainGraph = JApplicationGraphImpl(cp, usages)
        val ifdsGraph = JIRSafeApplicationGraph(JApplicationSingleExitGraph(mainGraph))

        val options = TaintAnalyzerOptions(
            ifdsTimeout = 1.minutes,
            ifdsApMode = apMode,
            markSet = markSet,
        )

        var markSetInput: MarkSetInput? = null
        var markSetOutcome: MarkSetOutcome? = null
        var confirmed: List<TaintSinkTracker.TaintVulnerability> = emptyList()
        var observedCoverage: MarkSetCoverage? = null
        var statusAfterPrescan: TaintAnalysisUnitRunnerManager.Status? = null

        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(options) {
            override val unrollStrategy: AnyAccessorUnrollStrategy
                get() = analysisUnrollStrategy

            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = ifdsGraph
            override fun analysisManager() =
                wrapManager(JIRAnalysisManager(cp, refManager, rulesProvider, markSetRecorder = createMarkSetRecorder()))
            override fun unitResolver() = SingleLocationUnit(cls.declaration.location)

            override fun onMarkSetPhase(input: MarkSetInput?, outcome: MarkSetOutcome) {
                markSetInput = input
                markSetOutcome = outcome
                statusAfterPrescan = ifdsEngine.status.get()
            }

            override fun onConfirmedVulnerabilities(vulnerabilities: List<TaintSinkTracker.TaintVulnerability>) {
                confirmed = vulnerabilities
            }

            override fun onMarkSetCoverage(coverage: MarkSetCoverage) {
                observedCoverage = coverage
            }
        }

        var markFacts: Set<MarkFactKey>? = null
        val findings = analyzer.use {
            it.analyzeWithIfds(eps).first.also { _ ->
                if (collectFacts) markFacts = markFactKeys(it.statementsWithFacts())
            }
        }
        return AnalysisRun(findings, confirmed, markSetInput, markSetOutcome, observedCoverage, markFacts, statusAfterPrescan)
    }

    fun assertReachable(
        config: SerializedTaintConfig,
        testCls: String,
        entryPointName: String,
        ruleId: String,
        testName: String,
    ) {
        val traces = runAnalysis(config, testCls, entryPointName)
        assertTrue(traces.isNotEmpty(), "$testName: expected taint to reach the sink, but no vulnerability was found")
        traces.forEach { vt ->
            assertEquals(
                ruleId, vt.vulnerability.rule.id,
                "$testName: unexpected rule id in vulnerability"
            )
        }
    }

    fun assertNotReachable(
        config: SerializedTaintConfig,
        testCls: String,
        entryPointName: String,
        testName: String,
    ) {
        val traces = runAnalysis(config, testCls, entryPointName)
        assertTrue(traces.isEmpty(), "$testName: expected no vulnerability, but found ${traces.size}")
    }
}
