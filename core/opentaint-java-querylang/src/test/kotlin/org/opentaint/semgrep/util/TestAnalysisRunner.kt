package org.opentaint.semgrep.util

import kotlinx.coroutines.runBlocking
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
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.markset.MarkSetCoverage
import org.opentaint.dataflow.ap.ifds.markset.MarkSetInput
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature
import org.opentaint.dataflow.jvm.ap.ifds.LambdaExpressionToAnonymousClassTransformerFeature
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.impl.features.classpaths.UnknownClasses
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.graph.JApplicationSingleExitGraph
import org.opentaint.jvm.graph.JMethodBoundaryInstFeature
import org.opentaint.jvm.sast.dataflow.JIRMethodExitRuleProvider
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.jvm.sast.rules.JIRSemgrepRuleProvider
import org.opentaint.jvm.transformer.JMultiDimArrayAllocationTransformer
import org.opentaint.jvm.transformer.JStringConcatTransformer
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import kotlin.time.Duration.Companion.minutes

/** Runs the samples of [samples]; [suite] names the test class in the differential summary line. */
class TestAnalysisRunner(
    private val samples: SamplesDb,
    private val suite: String = "querylang",
) : AutoCloseable {
    /** The differential switch (spec §8 Layer 3): `-PmarksetDiff=true` sets this system property. */
    private val markSetDiff: Boolean = System.getProperty("opentaint.markset.diff") == "true"

    /** `-PmarksetFlowSensitive=true`: the differential run uses option 3* (spec §9). */
    private val markSetFlowSensitive: Boolean = System.getProperty("opentaint.markset.flowSensitive") == "true"

    /** The mark-set outcomes of the differential pairs, logged by [close]. */
    private val differentialOutcomes = MarkSetOutcomeTally()

    private lateinit var cp: JIRClasspath

    init {
        initializeCp()
    }

    private fun initializeCp() = runBlocking {
        val lambdaAnonymousClass = LambdaAnonymousClassFeature()
        val lambdaTransformer = LambdaExpressionToAnonymousClassTransformerFeature(lambdaAnonymousClass)

        val features = mutableListOf(
            UnknownClasses, lambdaAnonymousClass, lambdaTransformer,
            JStringConcatTransformer, JMultiDimArrayAllocationTransformer,
            JMethodBoundaryInstFeature,
        )

        val allCpFiles = listOf(samples.samplesJar.toFile())
        cp = samples.db.classpath(allCpFiles, features)
    }

    override fun close() {
        if (markSetDiff) println(differentialOutcomes.summary(suite))
        cp.close()
    }

    private val ifdsAnalysisGraph by lazy {
        val usages = runBlocking { cp.usagesExt() }
        val mainGraph = JApplicationGraphImpl(cp, usages)
        JIRSafeApplicationGraph(JApplicationSingleExitGraph(mainGraph))
    }

    /**
     * One engine run: its findings, its mark-set phase outcome, its E1/E2 coverage (debug checks
     * only) and its marked facts for the E10 diff (with `collectFacts` only).
     */
    private class EngineRun(
        val findings: MarkSetFindings,
        val outcome: MarkSetOutcome?,
        val coverage: MarkSetCoverage?,
        val markFacts: Set<MarkFactKey>?,
    )

    private fun runEngine(
        configProvider: TaintRulesProvider,
        ep: JIRMethod,
        markSet: MarkSetScanOptions,
        collectFacts: Boolean = false,
    ): EngineRun {
        val options = TaintAnalyzerOptions(
            ifdsTimeout = 1.minutes,
            ifdsApMode = ApMode.Tree,
            markSet = markSet,
        )

        var confirmed: List<TaintSinkTracker.TaintVulnerability> = emptyList()
        var markSetOutcome: MarkSetOutcome? = null
        var observedCoverage: MarkSetCoverage? = null

        val analyzer = object : TaintAnalyzer<JIRMethod, JIRInst>(options) {
            override val unrollStrategy: AnyAccessorUnrollStrategy
                get() = AnyAccessorUnrollStrategy.AnyAccessorDisabled

            override fun analysisGraph() = ifdsAnalysisGraph
            override fun analysisManager() =
                JIRAnalysisManager(cp, refManager, configProvider, markSetRecorder = createMarkSetRecorder())
            override fun unitResolver() = object :JIRUnitResolver {
                override fun locationIsUnknown(loc: RegisteredLocation): Boolean =
                    loc.isRuntime

                override fun resolve(method: JIRMethod): UnitType =
                    if (method.enclosingClass.declaration.location.isRuntime) UnknownUnit else SingletonUnit

            }

            override fun onConfirmedVulnerabilities(vulnerabilities: List<TaintSinkTracker.TaintVulnerability>) {
                confirmed = vulnerabilities
            }

            override fun onMarkSetPhase(input: MarkSetInput?, outcome: MarkSetOutcome) {
                markSetOutcome = outcome
            }

            override fun onMarkSetCoverage(coverage: MarkSetCoverage) {
                observedCoverage = coverage
            }
        }

        var markFacts: Set<MarkFactKey>? = null
        val findings = analyzer.use {
            it.analyzeWithIfds(listOf(ep)).first.also { _ ->
                if (collectFacts) markFacts = markFactKeys(it.statementsWithFacts())
            }
        }
        return EngineRun(MarkSetFindings(confirmed, findings), markSetOutcome, observedCoverage, markFacts)
    }

    /**
     * Runs every sample's `entrypoint`. Under the differential switch (`-PmarksetDiff=true`, spec §8
     * Layer 3) each sample runs twice, the baseline and then the mark-set selection with the debug
     * checks on; the mark-set run must pass E1 and E2, the needed-mark facts must be equal per
     * statement (E10), and the confirmed findings before the trace filter (the contract's
     * comparison point, spec §2, E9) and the reported findings must be equal. A mark-set run that
     * fails open fails the sample: its differential would compare the baseline with itself. The
     * baseline's findings are returned.
     */
    fun run(
        rule: TaintRuleFromSemgrep<SerializedItem>,
        config: SerializedTaintConfig,
        useDefaultConfig: Boolean,
        samples: Set<String>
    ): Map<String, List<VulnerabilityWithTrace>> =
        samples.associate { sample ->
            val cls = cp.findClassOrNull(sample) ?: error("No sample in CP")
            val ep = cls.declaredMethods.singleOrNull { it.name == "entrypoint" }
                ?: error("No entrypoint in $sample")

            val baseline = runEngine(
                rulesProvider(rule, config, useDefaultConfig), ep, MarkSetScanOptions(enabled = false), collectFacts = markSetDiff,
            )
            if (markSetDiff) {
                val markSet = runEngine(
                    rulesProvider(rule, config, useDefaultConfig), ep,
                    MarkSetScanOptions(enabled = true, flowSensitive = markSetFlowSensitive, debugChecks = true),
                    collectFacts = true,
                )
                differentialOutcomes.record(markSet.outcome)
                assertMarkSetDebugChecks(
                    checkNotNull(baseline.markFacts), checkNotNull(markSet.markFacts),
                    markSet.outcome, markSet.coverage, sample,
                )
                assertSameMarkSetFindings(baseline.findings, markSet.findings, sample)
            }

            sample to baseline.findings.reported
        }

    private val defaultConfig by lazy {
        JavaDefaultConfigLoader.loadConfig()
            ?: error("Error while loading default config")
    }

    private fun rulesProvider(
        rule: TaintRuleFromSemgrep<SerializedItem>,
        config: SerializedTaintConfig,
        useDefaultConfig: Boolean
    ): TaintRulesProvider {
        val taintConfig = TaintConfiguration(cp)
        taintConfig.loadConfig(config)

        if (useDefaultConfig) {
            val defaultPassRules = SerializedTaintConfig(passThrough = defaultConfig.passThrough)
            taintConfig.loadConfig(defaultPassRules)
        }

        var cfg: TaintRulesProvider = JIRSemgrepRuleProvider(listOf(rule), taintConfig)
        cfg = JIRMethodExitRuleProvider(cfg)
        return cfg
    }
}
