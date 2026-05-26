package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.go.config.GoConfigLoader
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.jvm.sast.dataflow.DummySerializationContext
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toGoTaintConfiguration
import org.opentaint.util.analysis.ApplicationGraph
import java.io.File
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.test.fail
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoRuleDevSampleTest {
    private val samplesDir: Path by lazy {
        val prop = System.getProperty("GO_MASSIVE_SAMPLES_DIR")
            ?: error("System property GO_MASSIVE_SAMPLES_DIR not set; check build.gradle.kts wiring")
        Path(prop).also { require(it.toFile().isDirectory) }
    }

    private val rulesDir: Path by lazy {
        val prop = System.getProperty("OPENTAINT_GO_DEV_RULES_DIR")
            ?: error("System property OPENTAINT_GO_DEV_RULES_DIR not set; check build.gradle.kts wiring")
        Path(prop).also { require(it.toFile().isDirectory) }
    }

    private val client: GoIRClient by lazy { GoIRClient() }

    @AfterAll
    fun tearDown() { client.close() }

    @ParameterizedTest(name = "{0}")
    @MethodSource("discoverSamples")
    fun ruleDevSample(name: String) = runSample(name)

    @Suppress("unused")
    fun discoverSamples(): List<String> {
        val prefixes = listOf("cmdinj_", "path_", "sqlinj_", "xss_")
        val root = samplesDir.toFile()
        if (!root.isDirectory) return emptyList()
        return root.listFiles { f -> f.isDirectory && prefixes.any { f.name.startsWith(it) } }
            ?.sortedBy { it.name }
            ?.map { it.name }
            ?: emptyList()
    }

    private fun ruleFor(prefix: String): String = when (prefix) {
        "cmdinj" -> "cmdinj.yaml"
        "path" -> "path-traversal.yaml"
        "sqlinj" -> "sql-injection.yaml"
        "xss" -> "xss.yaml"
        else -> error("Unknown prefix: $prefix")
    }

    private fun runSample(name: String) {
        val sampleDir = samplesDir.resolve(name)
        val prefix = name.substringBefore('_')
        val ruleFile = rulesDir.resolve(ruleFor(prefix)).toFile()
        if (!ruleFile.isFile) fail("Rule file missing: $ruleFile")

        val program = client.buildFromDir(sampleDir, "./...")
        try {
            val config = loadConfig(ruleFile)
            GoConfigLoader.getConfig()?.let { config.loadConfig(it) }

            val entries = program.allFunctions().filter {
                it.pkg?.importPath == "util" && !it.isSynthetic && it.hasBody &&
                    it.parent == null &&
                    (it.name.startsWith("Positive_") || it.name.startsWith("Negative_"))
            }
            if (entries.isEmpty()) fail("[$name] no Positive_*/Negative_* entries")

            val failures = mutableListOf<String>()
            for (entry in entries) {
                val vulns = runAnalysis(program, config, entry)
                val isPositive = entry.name.startsWith("Positive_")
                if (isPositive && vulns.isEmpty()) failures += "Positive ${entry.fullName} reported NO vuln"
                if (!isPositive && vulns.isNotEmpty()) failures += "Negative ${entry.fullName} reported ${vulns.size}"
            }
            if (failures.isNotEmpty()) fail("[$name] " + failures.joinToString("; "))
        } finally {
            (program as? AutoCloseable)?.close()
        }
    }

    private fun loadConfig(yamlFile: File): GoTaintConfiguration {
        val yaml = yamlFile.readText()
        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
        val loaded = loader.loadRules()
        val rule = loaded.rulesWithMeta.firstOrNull() ?: fail("No rules loaded from ${yamlFile.name}")
        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<GoSerializedItem>
        return typed.toGoTaintConfiguration()
    }

    private fun runAnalysis(program: GoIRProgram, config: GoTaintConfiguration, entry: GoIRFunction): List<*> {
        val ifdsGraph = GoApplicationGraph(program, UtilUnitResolver)
        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(program, config),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = UtilUnitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )
        val start = MethodWithContext(entry, EmptyMethodContext)
        return engine.use { it.runAnalysis(listOf(start), 1.minutes, 10.seconds); it.getVulnerabilities() }
    }

    private object UtilUnitResolver : UnitResolver<GoIRFunction> {
        override fun resolve(method: GoIRFunction): UnitType =
            if (method.pkg?.importPath == "util") SingletonUnit else UnknownUnit
    }
}
