package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkSetFindings
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.common.sast.dataflow.assertSameMarkSetFindings
import org.opentaint.config.JavaDefaultConfigLoader
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
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

/** The mark-set options a differential run uses when the caller did not ask for mark-set mode. */
val defaultDifferentialMarkSet: MarkSetScanOptions
    get() = MarkSetScanOptions(
        enabled = true,
        flowSensitive = System.getProperty(MARKSET_FLOW_SENSITIVE_PROPERTY) == "true",
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
     * Layer 3) it runs twice, the baseline and then the mark-set selection, asserts that both report
     * the same findings, and returns the baseline's. The mark-set run is the requested one when
     * [markSet] is enabled, else [defaultDifferentialMarkSet]. [lastMarkSetInput] and
     * [lastMarkSetOutcome] describe the requested run only.
     */
    fun runAnalysis(
        config: SerializedTaintConfig,
        entryPointClass: String,
        entryPointMethods: List<String>,
        markSet: MarkSetScanOptions = this.markSet,
    ): List<VulnerabilityWithTrace> {
        if (!markSetDiff) return runAnalysisOnce(config, entryPointClass, entryPointMethods, markSet).publish()

        val markSetOptions = if (markSet.enabled) markSet else defaultDifferentialMarkSet
        val baseline = runAnalysisOnce(config, entryPointClass, entryPointMethods, MarkSetScanOptions())
        val restricted = runAnalysisOnce(config, entryPointClass, entryPointMethods, markSetOptions)
        assertSameMarkSetFindings(baseline.gated, restricted.gated, "$entryPointClass$entryPointMethods")

        (if (markSet.enabled) restricted else baseline).publish()
        return baseline.findings
    }

    /**
     * One run: its reported findings, its confirmed findings before the trace filter (spec E9),
     * and its mark-set phase observations.
     */
    class AnalysisRun(
        val findings: List<VulnerabilityWithTrace>,
        val confirmed: List<TaintSinkTracker.TaintVulnerability>,
        val markSetInput: MarkSetInput?,
        val markSetOutcome: MarkSetOutcome?,
    ) {
        /** The findings the differential gate compares. */
        val gated: MarkSetFindings get() = MarkSetFindings(confirmed, findings)
    }

    private fun AnalysisRun.publish(): List<VulnerabilityWithTrace> {
        lastMarkSetInput = markSetInput
        lastMarkSetOutcome = markSetOutcome
        return findings
    }

    /** Runs the analysis once with [markSet]; does not touch [lastMarkSetInput] / [lastMarkSetOutcome]. */
    fun runAnalysisOnce(
        config: SerializedTaintConfig,
        entryPointClass: String,
        entryPointMethods: List<String>,
        markSet: MarkSetScanOptions,
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

        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(options) {
            override val unrollStrategy: AnyAccessorUnrollStrategy
                get() = analysisUnrollStrategy

            override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> = ifdsGraph
            override fun analysisManager() =
                JIRAnalysisManager(cp, refManager, rulesProvider, markSetRecorder = createMarkSetRecorder())
            override fun unitResolver() = SingleLocationUnit(cls.declaration.location)

            override fun onMarkSetPhase(input: MarkSetInput?, outcome: MarkSetOutcome) {
                markSetInput = input
                markSetOutcome = outcome
            }

            override fun onConfirmedVulnerabilities(vulnerabilities: List<TaintSinkTracker.TaintVulnerability>) {
                confirmed = vulnerabilities
            }
        }

        val findings = analyzer.use {
            it.analyzeWithIfds(eps).first
        }
        return AnalysisRun(findings, confirmed, markSetInput, markSetOutcome)
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
