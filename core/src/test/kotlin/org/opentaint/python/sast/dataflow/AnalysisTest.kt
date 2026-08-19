package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.Result
import org.opentaint.dataflow.configuration.python.TaintAssignAction
import org.opentaint.dataflow.configuration.python.TaintCleaner
import org.opentaint.dataflow.configuration.python.TaintEntryPointSource
import org.opentaint.dataflow.configuration.python.TaintExitSink
import org.opentaint.dataflow.configuration.python.TaintMark
import org.opentaint.dataflow.configuration.python.TaintPassThrough
import org.opentaint.dataflow.configuration.python.TaintSink
import org.opentaint.dataflow.configuration.python.TaintSinkMeta
import org.opentaint.dataflow.configuration.python.TaintSource
import org.opentaint.dataflow.configuration.python.Target
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.python.rules.PIRCombinedTaintRulesProvider
import org.opentaint.dataflow.python.rules.PIRConfigTaintRulesProvider
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.dataflow.python.rules.PIRTaintRulesProvider
import org.opentaint.dataflow.python.rules.loadDefaultConfig
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.PythonLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toSerializedPythonTaintConfig
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
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
import kotlin.io.path.readText
import kotlin.io.path.relativeTo
import kotlin.io.path.toPath
import kotlin.io.path.walk
import kotlin.io.path.writeText
import kotlin.io.readText
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.minutes
import kotlin.use

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class AnalysisTest {
    lateinit var sourcesDir: Path
    lateinit var cp: PIRClasspath

    open val externalMethods: ExternalMethodTracker? = null

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
        source: TestSource,
        sink: TestSink,
        entryPointFunction: String
    ) {
        val vulnerabilities = runAnalysis(source, sink, entryPointFunction)
        assertTrue(vulnerabilities.isNotEmpty(), "Sink was not reached")
    }

    fun assertSinkNotReachable(
        source: TestSource,
        sink: TestSink,
        entryPointFunction: String
    ) {
        val vulnerabilities = runAnalysis(source, sink, entryPointFunction)
        assertTrue(vulnerabilities.isEmpty(), "Sink should not be reached")
    }

    private fun shippedRules(): PIRTaintRulesProvider = loadDefaultConfig()

    protected fun loadSemgrepRules(resourceDir: String): PIRConfigTaintRulesProvider {
        val rulesRoot = javaClass.getResource(resourceDir)?.toURI()?.toPath()
            ?: error("Missing rule dir $resourceDir")

        val loader = SemgrepRuleLoader(listOf(PythonLanguageStrategy()))
        val trace = SemgrepLoadTrace()
        rulesRoot.walk().filter { it.extension == "yaml" || it.extension == "yml" }.forEach { rulePath ->
            loader.registerRuleSet(rulePath.readText(), rulePath.relativeTo(rulesRoot), rulesRoot, trace)
        }

        val taintConfig = PIRTaintConfiguration()
        loader.loadRules().rulesWithMeta.forEach { rule ->
            @Suppress("UNCHECKED_CAST")
            val typed = rule.first as TaintRuleFromSemgrep<SerializedPythonRule>
            taintConfig.loadConfig(typed.toSerializedPythonTaintConfig())
        }

        return PIRConfigTaintRulesProvider(taintConfig)
    }

    fun runAnalysis(
        source: TestSource,
        sink: TestSink,
        entryPointFunction: String,
    ): List<VulnerabilityWithTrace> = runAnalysis(rulesWith(source, sink), entryPointFunction)

    fun runAnalysis(
        taintConfig: PIRTaintRulesProvider,
        entryPointFunction: String,
    ): List<VulnerabilityWithTrace> {
        val entryPoint = cp.findFunctionOrNull(entryPointFunction)
            ?: error("Entry point not found")

        val options = TaintAnalyzerOptions(
            ifdsTimeout = 10.minutes,
            ifdsApMode = ApMode.Tree,
        )

        val analyzer = PIRTaintAnalyzer(
            cp, taintConfig, UnitResolver { SingletonUnit }, options, externalMethods,
        )

        return analyzer.use { it.analyzeWithIfds(listOf(entryPoint)).first }
    }

    // region Test-only rule builders: declare per-fixture source / sink rules
    // inline and layer them over the shipped config (stdlib pass-throughs,
    // library rules) via PIRCombinedTaintRulesProvider.
    protected fun source(function: String, mark: String, pos: Position): TestSource =
        TestSource.Method(function, mark, pos)

    protected fun attributeSource(attribute: String, mark: String): TestSource =
        TestSource.Attribute(attribute, mark)

    protected fun sink(function: String, mark: String, pos: Position, id: String): TestSink =
        TestSink(function, mark, pos, id)

    private fun rulesWith(source: TestSource, sink: TestSink): PIRTaintRulesProvider =
        PIRCombinedTaintRulesProvider(
            loadDefaultConfig(),
            TestRulesProvider(listOf(source), listOf(sink)),
            PIRCombinedTaintRulesProvider.CombinationOptions(
                source = PIRCombinedTaintRulesProvider.CombinationMode.EXTEND,
                sink = PIRCombinedTaintRulesProvider.CombinationMode.EXTEND,
            ),
        )
    // endregion
}

sealed interface TestSource {
    fun rulesForMethod(method: PIRFunction): List<TaintSource> = emptyList()
    fun rulesForAttribute(name: String): List<TaintSource> = emptyList()

    /** Synthetic per-fixture source rule: taints [pos] of [function]'s call with [mark]. */
    data class Method(val function: String, val mark: String, val pos: Position) : TestSource {
        override fun rulesForMethod(method: PIRFunction): List<TaintSource> {
            if (!method.matches(function)) return emptyList()
            return listOf(
                TaintSource(Target.Function(method), mkTrue(), listOf(TaintAssignAction(TaintMark(mark), pos)))
            )
        }
    }

    data class Attribute(val attribute: String, val mark: String) : TestSource {
        override fun rulesForAttribute(name: String): List<TaintSource> {
            if (name != attribute && !name.endsWith(".$attribute")) return emptyList()
            return listOf(
                TaintSource(Target.Attribute(name), mkTrue(), listOf(TaintAssignAction(TaintMark(mark), Result)))
            )
        }
    }
}

/** Synthetic per-fixture sink rule: flags when [mark] reaches [pos] of [function]. */
data class TestSink(val function: String, val mark: String, val pos: Position, val id: String)

/**
 * In-place [PIRTaintRulesProvider] over synthetic [TestSource] / [TestSink] rules.
 * Matches a call by fully-qualified name (constructor calls also match the class
 * FQN) and emits the compiled runtime rule directly — no serialized config.
 */
private class TestRulesProvider(
    private val sources: List<TestSource>,
    private val sinks: List<TestSink>,
) : PIRTaintRulesProvider {
    override fun sourcesForMethod(method: PIRFunction): List<TaintSource> =
        sources.flatMap { it.rulesForMethod(method) }

    override fun sinksForMethod(method: PIRFunction): List<TaintSink> =
        sinks.filter { method.matches(it.function) }.map {
            TaintSink(
                target = Target.Function(method),
                condition = CommonCondition.Atom(ContainsMark(TaintMark(it.mark), it.pos)),
                id = it.id,
                meta = TaintSinkMeta(it.id, CommonTaintConfigurationSinkMeta.Severity.Warning, cwe = null, note = it.id),
            )
        }

    override fun exitSinksForMethod(method: PIRFunction): List<TaintExitSink> = emptyList()

    override fun entryPointSourcesForMethod(method: PIRFunction): List<TaintEntryPointSource> = emptyList()
    override fun passThroughForMethod(method: PIRFunction, bySimpleName: Boolean): List<TaintPassThrough> = emptyList()
    override fun cleanersForMethod(method: PIRFunction): List<TaintCleaner> = emptyList()
    override fun sourcesForAttribute(name: String): List<TaintSource> =
        sources.flatMap { it.rulesForAttribute(name) }
    override fun sinksForAttribute(name: String): List<TaintSink> = emptyList()
    override fun passThroughForAttribute(name: String): List<TaintPassThrough> = emptyList()
    override fun cleanersForAttribute(name: String): List<TaintCleaner> = emptyList()
}

private fun PIRFunction.matches(name: String): Boolean {
    val qn = qualifiedName
    val ctorQn = if (enclosingClass != null) qn.removeSuffix(".__init__") else qn
    return qn == name || ctorQn == name
}
