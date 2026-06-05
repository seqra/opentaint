package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedGlobalSource
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.Sink
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.Source
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.ext.findFunctionByFullName
import org.opentaint.ir.go.inst.GoIRInst
import java.nio.file.Path
import java.util.jar.JarFile
import kotlin.io.bufferedReader
import kotlin.io.deleteRecursively
import kotlin.io.path.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.io.print
import kotlin.io.readText
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.minutes
import kotlin.use

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class AnalysisTest {
    lateinit var sourcesDir: Path
    lateinit var cp: GoIRProgram
    lateinit var client: GoIRClient

    // Standard source/sink rules
    val stdSource = Source(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("Source"),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
    )
    val stdSink = Sink(
        pkg = GoNameMatcher.Simple("util"),
        function = GoNameMatcher.Simple("Sink"),
        condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = GoSinkMetaData("Taint sink: test/util.Sink"),
        info = null
    )

    @BeforeAll
    fun setup() {
        val jarPath = System.getenv("TEST_SAMPLES_JAR")
            ?: error("TEST_SAMPLES_JAR environment variable not set. Run tests via Gradle.")

        client = GoIRClient()

        sourcesDir = createTempDirectory("go-sources")
        extractGoSourcesFromJar(Path(jarPath), sourcesDir)

        cp = createClasspath()
    }

    @AfterAll
    fun tearDown() {
        if (::client.isInitialized) client.close()
        if (::sourcesDir.isInitialized) {
            sourcesDir.toFile().deleteRecursively()
        }
    }

    private fun createClasspath(): GoIRProgram {
        return client.buildFromDir(sourcesDir, GoIRLoadConfig()).program
    }

    private fun extractGoSourcesFromJar(jarPath: Path, targetDir: Path) {
        JarFile(jarPath.toFile()).use { jar ->
            jar.entries().asSequence()
                .filter { it.name.endsWith(".go") || it.name.endsWith(".mod") }
                .forEach { entry ->
                    val targetFile = targetDir.resolve(entry.name)
                    targetFile.parent.createDirectories()
                    jar.getInputStream(entry).use { input ->
                        targetFile.writeText(input.bufferedReader().readText())
                    }
                }
        }
    }

    open val commonPassRules: List<PassThrough> = emptyList()

    // Convenience: standard assertion with default rules
    fun assertReachable(fn: String) = assertSinkReachable(stdSource, stdSink, fn)
    fun assertNotReachable(fn: String) = assertSinkNotReachable(stdSource, stdSink, fn)

    fun assertSinkReachable(
        source: Source,
        sink: Sink,
        entryPointFunction: String,
    ) {
        val vulnerabilities = runAnalysis(source, sink, entryPointFunction)
        assertTrue(vulnerabilities.isNotEmpty(), "Sink was not reached in $entryPointFunction")
    }

    fun assertSinkNotReachable(
        source: Source,
        sink: Sink,
        entryPointFunction: String,
    ) {
        val vulnerabilities = runAnalysis(source, sink, entryPointFunction)
        assertTrue(vulnerabilities.isEmpty(), "Sink should not be reached in $entryPointFunction")
    }

    fun runAnalysisWithGlobalSource(
        globalSource: GoSerializedGlobalSource,
        sink: Sink,
        entryPointFunction: String,
        extraPassRules: List<PassThrough> = emptyList(),
    ): List<VulnerabilityWithTrace> {
        val allPassRules = commonPassRules + extraPassRules
        val serializedConfig = GoSerializedTaintConfig(
            globalSource = listOf(globalSource),
            sink = listOf(sink),
            passThrough = allPassRules,
        )
        return runAnalysisOnConfig(serializedConfig, entryPointFunction)
    }

    fun runAnalysis(
        source: Source,
        sink: Sink,
        entryPointFunction: String,
        extraPassRules: List<PassThrough> = emptyList(),
    ): List<VulnerabilityWithTrace> {
        val allPassRules = commonPassRules + extraPassRules
        val serializedConfig = GoSerializedTaintConfig(
            source = listOf(source), sink = listOf(sink), passThrough = allPassRules
        )
        return runAnalysisOnConfig(serializedConfig, entryPointFunction)
    }

    fun printFactsAt(
        entryPointFunction: String,
        source: Source = stdSource,
        sink: Sink = stdSink,
        extraPassRules: List<PassThrough> = emptyList(),
    ) {
        val allPassRules = commonPassRules + extraPassRules
        val serializedConfig = GoSerializedTaintConfig(
            source = listOf(source), sink = listOf(sink), passThrough = allPassRules
        )

        runAnalysisOnConfig(serializedConfig, entryPointFunction, printFacts = true)
    }

    private fun runAnalysisOnConfig(
        serializedConfig: GoSerializedTaintConfig,
        entryPointFunction: String,
        printFacts: Boolean = false,
    ): List<VulnerabilityWithTrace> {
        val entryPoint = cp.findFunctionByFullName(entryPointFunction)
            ?: error("Entry point not found: $entryPointFunction")

        val loadedConfig = GoTaintConfiguration()
        loadedConfig.loadConfig(serializedConfig)

        val options = CommonAnalysisOptions(
            ifdsAnalysisTimeout = 1.minutes
        )
        val analyzer = GoTaintAnalyzer(cp, loadedConfig, GoTestUnitResolver, options.taintAnalyzerOptions())
        analyzer.use {
            val result = it.analyzeWithIfds(listOf(entryPoint))
            if (printFacts) {
                it.printFacts(entryPoint)
            }
            return result.first
        }
    }

    internal object GoTestUnitResolver : UnitResolver<GoIRFunction> {
        override fun resolve(method: GoIRFunction): UnitType {
            val pkgName = method.pkg?.importPath ?: return UnknownUnit
            return when {
                pkgName == "test" -> SingletonUnit
                pkgName == "test/util" -> UnknownUnit
                // Stdlib / external dependencies the sample may import (strings,
                // container/list, sync/atomic, …) — treat as opaque so the
                // analysis still runs.
                else -> UnknownUnit
            }
        }
    }

    private fun GoTaintAnalyzer.printFacts(entryPoint: GoIRFunction) {
        @Suppress("UNCHECKED_CAST")
        val allFacts = statementsWithFacts() as Map<GoIRInst, Set<FinalFactAp>>

        val sb = StringBuilder()
        sb.appendLine("=== Facts at $entryPoint ===")
        val body = entryPoint.body
        if (body == null) {
            sb.appendLine("  (no body)")
        } else {
            val sortedInsts = body.instructions.sortedWith(
                compareBy(
                    { it.location.blockIndex },
                    { it.location.index },
                )
            )
            for (stmt in sortedInsts) {
                val loc = stmt.location
                val line = loc.position?.line ?: -1
                val coord = "${loc.blockIndex}:${loc.index}"
                val facts = allFacts[stmt].orEmpty()
                val factStr = if (facts.isEmpty()) "∅" else facts.joinToString(", ") { it.toString() }
                sb.appendLine("  L${line.toString().padStart(3)} [$coord]  $stmt    facts: $factStr")
            }
        }
        val report = sb.toString()
        print(report)
    }
}
