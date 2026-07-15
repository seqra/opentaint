package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.go.config.GoDefaultConfigLoader
import org.opentaint.go.sast.rules.GoSemgrepRuleProvider
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.go.pattern.conversion.loadGoTaintConfiguration
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import java.io.File
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.test.assertTrue
import kotlin.test.fail
import kotlin.time.Duration.Companion.minutes

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class GoSampleBasedTestBase(val samplesDirProperty: String) {
    private val samplesDir: Path by lazy {
        val prop = System.getProperty(samplesDirProperty)
            ?: error("System property $samplesDirProperty not set; check build.gradle.kts wiring")
        Path(prop).also {
            require(it.toFile().isDirectory) { "$samplesDirProperty is not a directory: $it" }
        }
    }

    private val client: GoIRClient by lazy { GoIRClient() }

    private val program: GoIRProgram by lazy {
        client.buildFromDir(samplesDir, GoIRLoadConfig()).program
    }

    open val tracker: ExternalMethodTracker? = null

    open fun onTearDown() {}

    @AfterAll
    fun tearDown() {
        client.close()
        onTearDown()
    }

    val defaultApproximationsConfig by lazy {
        GoDefaultConfigLoader.loadConfig()
    }

    fun runSample(ruleName: String, useDefaultConfig: Boolean = false) {
        val sampleDir = samplesDir.resolve(ruleName)
        require(sampleDir.toFile().isDirectory) {
            "Sample directory missing: $sampleDir"
        }

        val yamlFile = sampleDir.toFile().listFiles { f -> f.extension == "yaml" }
            ?.singleOrNull()
            ?: fail("Expected exactly one *.yaml rule under $sampleDir")
        val rulesProvider = { loadRulesProvider(yamlFile, useDefaultConfig) }

        val samplePkgImportPath = "$MODULE_NAME/$ruleName"
        val pkg = program.findPackage(samplePkgImportPath)
            ?: error("Could not find package $samplePkgImportPath")

        val resolver = SamplePkgUnitResolver(samplePkgImportPath)

        val entries = pkg.functions.filter {
            !it.isSynthetic &&
                    it.hasBody &&
                    it.parent == null &&
                    (it.name.startsWith("Positive_") || it.name.startsWith("Negative_"))
        }

        check(entries.isNotEmpty()) {
            "No Positive_*/Negative_* top-level entry points found in $sampleDir " +
                    "(seen: ${program.allFunctions().map { it.fullName }})"
        }

        for (entry in entries) {
            val result = runAnalysis(rulesProvider(), entry, resolver)
            val isPositive = entry.name.startsWith("Positive_")
            if (isPositive) {
                assertTrue(
                    result.traceResolved,
                    "[$ruleName] Positive entry ${entry.fullName} ${if (result.vulnerabilityReported) "NO TRACE" else "NO VULNERABILITY"}",
                )
            } else {
                assertTrue(
                    !result.traceResolved,
                    "[$ruleName] Negative entry ${entry.fullName} reported vulnerabilities: $result",
                )
            }
        }
    }

    private fun loadRulesProvider(yamlFile: File, useDefaultConfig: Boolean): GoTaintRulesProvider {
        val yaml = yamlFile.readText()
        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
        val loadedRules = loader.loadRules()
        val rule = loadedRules.rulesWithMeta.firstOrNull()
            ?: fail("No rules loaded from $yamlFile")

        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<GoSerializedItem>
        val config = GoTaintConfiguration().loadGoTaintConfiguration(typed)
        if (useDefaultConfig) {
            val defaultConfig = defaultApproximationsConfig
                ?: fail("Bundled go-config not found on classpath")
            config.loadConfig(defaultConfig)
        }
        return GoSemgrepRuleProvider(listOf(typed), config)
    }

    data class AnalysisResult(
        val vulnerabilityReported: Boolean,
        val traceResolved: Boolean,
    )

    private fun runAnalysis(
        rulesProvider: GoTaintRulesProvider,
        entryPoint: GoIRFunction,
        resolver: UnitResolver<GoIRFunction>,
    ): AnalysisResult {
        val ifdsGraph = GoApplicationGraph(program, resolver)

        val options = TaintAnalyzerOptions(
            ifdsTimeout = 1.minutes,
            ifdsApMode = ApMode.BaseOnlyField
        )

        val analyzer = object : TaintAnalyzer<GoIRFunction, GoIRInst>(options) {
            override val unrollStrategy: AnyAccessorUnrollStrategy get() = AnyUnrollStrategy
            override fun analysisGraph() = ifdsGraph
            override fun analysisManager() = GoAnalysisManager(program, rulesProvider, tracker)
            override fun unitResolver() = resolver
        }

        return analyzer.use { eng ->
            val resolvedTraces = eng.analyzeWithIfds(listOf(entryPoint)).first
            val vulns = eng.ifdsEngine.getVulnerabilities()
            AnalysisResult(vulns.isNotEmpty(), resolvedTraces.isNotEmpty())
        }
    }

    private object AnyUnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private class SamplePkgUnitResolver(
        private val samplePkgImportPath: String,
    ) : UnitResolver<GoIRFunction> {
        override fun resolve(method: GoIRFunction): UnitType {
            val pkg = method.pkg?.importPath ?: return UnknownUnit
            return if (pkg.startsWith(samplePkgImportPath)) SingletonUnit else UnknownUnit
        }
    }

    companion object {
        private const val MODULE_NAME = "samples"
    }
}
