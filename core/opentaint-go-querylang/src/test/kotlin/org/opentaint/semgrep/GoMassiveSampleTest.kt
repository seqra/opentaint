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
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
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
import kotlin.io.path.writeText
import kotlin.test.fail
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

/**
 * Parameterized driver for the "massive" sample tree under `samples-go-massive/`.
 * Auto-discovers every direct subdirectory and runs it through the same pipeline
 * as [GoSampleBasedTest.runSample] — but with the bundled go-config merged in
 * (useDefaultConfig=true) and a shared [ExternalMethodTracker] aggregating
 * unresolved library calls across the whole batch.
 *
 * On @AfterAll the tracker dumps to `build/go-external-methods.json`.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoMassiveSampleTest {

    private val samplesDir: Path by lazy {
        val prop = System.getProperty("GO_MASSIVE_SAMPLES_DIR")
            ?: error("System property GO_MASSIVE_SAMPLES_DIR not set; check build.gradle.kts wiring")
        Path(prop).also {
            require(it.toFile().isDirectory) { "GO_MASSIVE_SAMPLES_DIR is not a directory: $it" }
        }
    }

    private val outputDir: Path by lazy {
        val prop = System.getProperty("GO_MASSIVE_OUTPUT_DIR")
            ?: error("System property GO_MASSIVE_OUTPUT_DIR not set; check build.gradle.kts wiring")
        Path(prop).also { it.toFile().mkdirs() }
    }

    private val client: GoIRClient by lazy { GoIRClient() }
    private val tracker = ExternalMethodTracker()
    private val perSampleNotes = mutableListOf<String>()

    @AfterAll
    fun tearDown() {
        client.close()

        val ext = tracker.getExternalMethods()
        val withoutRules = ext.withoutRules.joinToString("\n") {
            "${it.callSites.toString().padStart(4)}  ${it.method}  [${it.factPositions.joinToString(",")}]"
        }
        val withRules = ext.withRules.joinToString("\n") {
            "${it.callSites.toString().padStart(4)}  ${it.method}  [${it.factPositions.joinToString(",")}]"
        }
        outputDir.resolve("external-methods-without-rules.txt").writeText(withoutRules + "\n")
        outputDir.resolve("external-methods-with-rules.txt").writeText(withRules + "\n")
        if (perSampleNotes.isNotEmpty()) {
            outputDir.resolve("per-sample-notes.txt").writeText(perSampleNotes.joinToString("\n") + "\n")
        }
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("discoverSamples")
    fun massiveSample(name: String) = runSample(name)

    @Suppress("unused")
    fun discoverSamples(): List<String> {
        val root = samplesDir.toFile()
        if (!root.isDirectory) return emptyList()
        return root.listFiles { f -> f.isDirectory }
            ?.sortedBy { it.name }
            ?.map { it.name }
            ?: emptyList()
    }

    private fun runSample(name: String) {
        val sampleDir = samplesDir.resolve(name)
        val yamlFile = sampleDir.toFile().listFiles { f -> f.extension == "yaml" }
            ?.singleOrNull()
            ?: fail("[$name] expected exactly one *.yaml rule under $sampleDir")

        val program = try {
            client.buildFromDir(sampleDir, "./...")
        } catch (e: Throwable) {
            perSampleNotes += "[$name] go build failed: ${e.message}"
            fail("[$name] go build failed: ${e.message}")
        }

        // Each sample opens a fresh Go SSA session that pins the full
        // `*ssa.Program` on the server. Across a 200-sample batch the unreleased
        // sessions exhaust JVM and server heap, so close per sample.
        try {
            val config = try {
                loadConfig(yamlFile)
            } catch (e: Throwable) {
                perSampleNotes += "[$name] rule load failed: ${e.message}"
                fail("[$name] rule load failed: ${e.message}")
            }
            config.loadConfig(GoConfigLoader.getConfig()!!)

            val entries = program.allFunctions().filter {
                it.pkg?.importPath == "util" && !it.isSynthetic && it.hasBody &&
                    // Skip nested anonymous functions (e.g. `Positive_closure$1`) — the
                    // taint source lives in the enclosing named function and the closure
                    // body on its own has nothing to flag.
                    it.parent == null &&
                    (it.name.startsWith("Positive_") || it.name.startsWith("Negative_"))
            }
            if (entries.isEmpty()) {
                perSampleNotes += "[$name] no Positive_*/Negative_* entries found"
                fail("[$name] no Positive_*/Negative_* entries found")
            }

            val failures = mutableListOf<String>()
            for (entry in entries) {
                val result = runAnalysis(program, config, entry)
                val positive = entry.name.startsWith("Positive_")
                if (positive) {
                    when {
                        result.rawVulns.isEmpty() ->
                            failures += "Positive ${entry.fullName} reported NO vuln"
                        result.tracedOk.isEmpty() ->
                            failures += "Positive ${entry.fullName} reported ${result.rawVulns.size} vuln(s) but trace did not resolve"
                        // else: tracedOk non-empty → PASS
                    }
                } else {
                    if (result.tracedOk.isNotEmpty()) {
                        failures += "Negative ${entry.fullName} reported ${result.tracedOk.size} traced vuln(s)"
                    }
                    // tracedOk empty (even with raw vulns) → PASS (trace filtered the FP)
                }
            }
            if (failures.isNotEmpty()) {
                perSampleNotes += "[$name] " + failures.joinToString("; ")
                fail("[$name] " + failures.joinToString("; "))
            }
        } finally {
            (program as? AutoCloseable)?.close()
        }
    }

    private fun loadConfig(yamlFile: File): GoTaintConfiguration {
        val yaml = yamlFile.readText()
        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path(yamlFile.name), Path("."), SemgrepLoadTrace())
        val loaded = loader.loadRules()
        val rule = loaded.rulesWithMeta.firstOrNull() ?: error("No rules loaded from ${yamlFile.name}")

        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<GoSerializedItem>
        return typed.toGoTaintConfiguration()
    }

    private data class AnalysisResult(
        val rawVulns: List<Any?>,
        val tracedOk: List<VulnerabilityWithTrace>,
        val tracedFail: List<VulnerabilityWithTrace>,
    )

    private fun runAnalysis(
        program: GoIRProgram,
        config: GoTaintConfiguration,
        entryPoint: GoIRFunction,
    ): AnalysisResult {
        val ifdsGraph = GoApplicationGraph(program, UtilUnitResolver)

        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(program, GoTaintRulesProvider(config), externalMethodTracker = tracker),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = UtilUnitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethod = MethodWithContext(entryPoint, EmptyMethodContext)
        return engine.use { eng ->
            eng.runAnalysis(listOf(startMethod), timeout = 1.minutes, cancellationTimeout = 10.seconds)
            val rawVulns = eng.getVulnerabilities()
            val traced = eng.resolveVulnerabilityTraces(
                setOf(entryPoint), rawVulns,
                resolverParams = TraceResolver.Params(),
                timeout = 1.minutes, cancellationTimeout = 10.seconds,
            )
            val tracedOk = traced.filter { it.trace != null }
            val tracedFail = traced.filter { it.trace == null }
            AnalysisResult(rawVulns, tracedOk, tracedFail)
        }
    }

    private object UtilUnitResolver : UnitResolver<GoIRFunction> {
        override fun resolve(method: GoIRFunction): UnitType =
            when (method.pkg?.importPath) {
                "util" -> SingletonUnit
                else -> UnknownUnit
            }
    }
}
