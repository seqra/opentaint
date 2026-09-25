package org.opentaint.semgrep.util

import kotlinx.coroutines.runBlocking
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.config.JavaDefaultConfigLoader
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
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
import org.opentaint.ir.api.common.cfg.CommonInst
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

class TestAnalysisRunner(
    private val samples: SamplesDb,
) : AutoCloseable {
    /** The differential switch (spec §8 Layer 3): `-PmarksetDiff=true` sets this system property. */
    private val markSetDiff: Boolean = System.getProperty("opentaint.markset.diff") == "true"

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
        cp.close()
    }

    private val ifdsAnalysisGraph by lazy {
        val usages = runBlocking { cp.usagesExt() }
        val mainGraph = JApplicationGraphImpl(cp, usages)
        JIRSafeApplicationGraph(JApplicationSingleExitGraph(mainGraph))
    }

    /** One run: its reported findings and its confirmed findings before the trace filter (spec E9). */
    private class Run(
        val findings: List<VulnerabilityWithTrace>,
        val confirmed: List<TaintSinkTracker.TaintVulnerability>,
    )

    private fun runEngine(configProvider: TaintRulesProvider, ep: JIRMethod, markSet: MarkSetScanOptions): Run {
        val options = TaintAnalyzerOptions(
            ifdsTimeout = 1.minutes,
            ifdsApMode = ApMode.Tree,
            markSet = markSet,
        )

        var confirmed: List<TaintSinkTracker.TaintVulnerability> = emptyList()

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
        }

        val findings = analyzer.use { it.analyzeWithIfds(listOf(ep)).first }
        return Run(findings, confirmed)
    }

    /**
     * Runs every sample's `entrypoint`. Under the differential switch (`-PmarksetDiff=true`, spec §8
     * Layer 3) each sample runs twice, the baseline and then the mark-set selection; the confirmed
     * findings before the trace filter (the contract's comparison point, spec §2, E9) and the
     * reported findings must be equal, and the baseline's are returned.
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

            val baseline = runEngine(rulesProvider(rule, config, useDefaultConfig), ep, MarkSetScanOptions())
            if (markSetDiff) {
                val markSet = runEngine(
                    rulesProvider(rule, config, useDefaultConfig), ep, MarkSetScanOptions(enabled = true)
                )
                assertSameKeys(baseline.confirmed.keys(), markSet.confirmed.keys(), "confirmed findings of $sample")
                assertSameKeys(
                    baseline.findings.map { it.vulnerability }.keys(),
                    markSet.findings.map { it.vulnerability }.keys(),
                    "reported findings of $sample",
                )
            }

            sample to baseline.findings
        }

    private fun List<TaintSinkTracker.TaintVulnerability>.keys(): Set<Pair<String, CommonInst>> =
        mapTo(hashSetOf()) { it.ruleId to it.statement }

    private fun assertSameKeys(
        baseline: Set<Pair<String, CommonInst>>,
        markSet: Set<Pair<String, CommonInst>>,
        what: String,
    ) {
        if (baseline == markSet) return

        fun Set<Pair<String, CommonInst>>.show() = map { (rule, stmt) -> "$rule @ ${stmt.location.method}: $stmt" }
        throw AssertionError(
            "mark-set differs from the baseline in the $what\n" +
                "  missing under mark-set: ${(baseline - markSet).show()}\n" +
                "  extra under mark-set: ${(markSet - baseline).show()}"
        )
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
