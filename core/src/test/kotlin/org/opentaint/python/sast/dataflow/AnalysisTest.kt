package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.DummySerializationContext
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonPosition
import org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase
import org.opentaint.dataflow.configuration.python.serialized.PythonSinkMetaData
import org.opentaint.dataflow.configuration.python.serialized.PythonTarget
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintAssignAction
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintConfig
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.python.analysis.PIRAnalysisManager
import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.dataflow.python.rules.PythonConfigLoader
import org.opentaint.dataflow.python.rules.TaintRules
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
import org.opentaint.util.analysis.ApplicationGraph
import java.nio.file.Path
import java.util.jar.JarFile
import kotlin.io.bufferedReader
import kotlin.io.deleteRecursively
import kotlin.io.path.Path
import kotlin.io.path.absolutePathString
import kotlin.io.path.createDirectories
import kotlin.io.path.createTempDirectory
import kotlin.io.path.extension
import kotlin.io.path.isRegularFile
import kotlin.io.path.walk
import kotlin.io.path.writeText
import kotlin.io.readText
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds
import kotlin.use

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class AnalysisTest {
    lateinit var sourcesDir: Path
    lateinit var cp: PIRClasspath

    @BeforeAll
    fun setup() {
        cp = initCp()
    }

    open fun initCp(): PIRClasspath {
        val jarPath = System.getenv("TEST_SAMPLES_JAR")
            ?: error("TEST_SAMPLES_JAR environment variable not set. Run tests via Gradle.")

        sourcesDir = createTempDirectory("python-sources")
        extractPythonSourcesFromJar(Path(jarPath), sourcesDir)

        val pyFiles = sourcesDir.walk()
            .filter { it.isRegularFile() && it.extension == "py" }
            .mapTo(mutableListOf()) { it.absolutePathString() }

        return createClasspath(pyFiles)
    }

    @AfterAll
    fun tearDown() {
        if (::cp.isInitialized) cp.close()
        if (::sourcesDir.isInitialized) {
            sourcesDir.toFile().deleteRecursively()
        }
    }

    private fun createClasspath(pyFiles: List<String>): PIRClasspath {
        return PIRClasspathLoader(
            PIRSettings(
                sources = pyFiles,
                mypyFlags = listOf(
                    "--ignore-missing-imports",
                    "--namespace-packages",
                    "--explicit-package-bases",
                ),
                rpcTimeout = java.time.Duration.ofSeconds(1200),
            )
        ).load()
    }

    private fun extractPythonSourcesFromJar(jarPath: Path, targetDir: Path) {
        JarFile(jarPath.toFile()).use { jar ->
            jar.entries().asSequence()
                .filter { it.name.endsWith(".py") }
                .forEach { entry ->
                    val targetFile = targetDir.resolve(entry.name)
                    targetFile.parent.createDirectories()
                    jar.getInputStream(entry).use { input ->
                        targetFile.writeText(input.bufferedReader().readText())
                    }
                }
        }
    }

    fun assertSinkReachable(
        entryPointFunction: String
    ) {
        val vulnerabilities = runAnalysis(shippedRules(), entryPointFunction)
        assertTrue(vulnerabilities.isNotEmpty(), "Sink was not reached")
    }

    fun assertSinkNotReachable(
        entryPointFunction: String
    ) {
        val vulnerabilities = runAnalysis(shippedRules(), entryPointFunction)
        assertTrue(vulnerabilities.isEmpty(), "Sink should not be reached")
    }

    fun assertSinkReachable(
        source: TaintRules.Source,
        sink: TaintRules.Sink,
        entryPointFunction: String
    ) {
        val taintRules = buildPirTaintConfiguration(listOf(source), listOf(sink))
        val vulnerabilities = runAnalysis(taintRules, entryPointFunction)
        assertTrue(vulnerabilities.isNotEmpty(), "Sink was not reached")
    }

    fun assertSinkNotReachable(
        source: TaintRules.Source,
        sink: TaintRules.Sink,
        entryPointFunction: String
    ) {
        val taintRules = buildPirTaintConfiguration(listOf(source), listOf(sink))
        val vulnerabilities = runAnalysis(taintRules, entryPointFunction)
        assertTrue(vulnerabilities.isEmpty(), "Sink should not be reached")
    }

    private fun shippedRules(): PIRTaintConfiguration {
        val serializedConfig = PythonConfigLoader.getConfig()
            ?: error("Couldn't resolve python config")
        return PIRTaintConfiguration(serializedConfig)
    }

    fun runAnalysis(
        taintConfig: PIRTaintConfiguration,
        entryPointFunction: String,
    ): List<TaintSinkTracker.TaintVulnerability> {
        val entryPoint = cp.findFunctionOrNull(entryPointFunction)
            ?: error("Entry point not found")

        val ifdsGraph = PIRApplicationGraph(cp)

        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            PIRAnalysisManager(cp, taintConfig),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = { SingletonUnit },
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethod = MethodWithContext(entryPoint, EmptyMethodContext)
        return engine.use { eng ->
            eng.runAnalysis(listOf(startMethod), timeout = 100.minutes, cancellationTimeout = 10.seconds)
            eng.getVulnerabilities()
        }
    }
}

// region Test-only adapter: layer the test's TaintRules.Source/Sink rules
// on top of the shipped YAML config (which already provides stdlib
// pass-throughs and other library rules) so each test can keep its
// per-fixture source / sink declarations inline.
// TODO introduce taintProvider interface
private fun buildPirTaintConfiguration(
    sources: List<TaintRules.Source>,
    sinks: List<TaintRules.Sink>,
): PIRTaintConfiguration {
    val shipped: SerializedPythonTaintConfig = PythonConfigLoader.getConfig()
        ?: SerializedPythonTaintConfig()

    val merged = SerializedPythonTaintConfig(
        entryPoint = shipped.entryPoint,
        source = shipped.source + sources.map { src ->
            SerializedPythonSource(
                target = PythonTarget.Function(src.function, null),
                condition = null,
                taint = listOf(SerializedPythonTaintAssignAction(
                    kind = src.mark,
                    pos = PythonPosition.BaseOnly(src.pos.toPython()),
                )),
            )
        },
        sink = shipped.sink + sinks.map { sk ->
            SerializedPythonSink(
                target = PythonTarget.Function(sk.function, null),
                condition = SerializedPythonCondition.ContainsMark(
                    tainted = sk.mark,
                    pos = PythonPosition.BaseOnly(sk.pos.toPython()),
                ),
                meta = PythonSinkMetaData(cwe = null, note = sk.id),
            )
        },
        passThrough = shipped.passThrough,
        cleaner = shipped.cleaner,
    )
    return PIRTaintConfiguration(merged)
}

private fun PositionBase.toPython(): PythonPositionBase = when (this) {
    is PositionBase.Argument -> PythonPositionBase.Argument(idx)
    PositionBase.Result -> PythonPositionBase.Result
    PositionBase.This -> PythonPositionBase.This
    is PositionBase.ClassStatic -> PythonPositionBase.ClassRef(className)
    is PositionBase.AnyArgument -> error("AnyArgument is not used in Python test rules")
}
// endregion
