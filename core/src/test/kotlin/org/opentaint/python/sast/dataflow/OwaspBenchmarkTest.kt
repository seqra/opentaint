package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.dataflow.python.rules.PIRCombinedTaintRulesProvider
import org.opentaint.dataflow.python.rules.PIRConfigTaintRulesProvider
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.dataflow.python.rules.PIRTaintRulesProvider
import org.opentaint.dataflow.python.rules.loadDefaultConfig
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.PythonLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toSerializedPythonTaintConfig
import java.nio.file.Path
import java.util.jar.JarFile
import kotlin.io.path.Path
import kotlin.io.path.absolutePathString
import kotlin.io.path.createDirectories
import kotlin.io.path.createTempDirectory
import kotlin.io.path.extension
import kotlin.io.path.isRegularFile
import kotlin.io.path.walk
import kotlin.io.path.writeText
import kotlin.test.assertTrue

/**
 * Runs the OWASP Benchmark for Python.
 *
 * Each entry is driven by a hand-written semgrep rule under
 * `core/src/test/resources/owasp-benchmark-rules/BenchmarkTest<id>.yaml` that encapsulates
 * that entry's source/sink/cleaner. The rule is layered over the pass-only shipped config
 * (`loadDefaultConfig()` now holds only pass-through rules) via [PIRCombinedTaintRulesProvider].
 * Ground truth is hardcoded per `@Test` (assert reachable/not-reachable), taken from the OWASP
 * `expectedresults-0.1.csv`.
 *
 * A shared [ExternalMethodTracker] aggregates the library methods where taint was dropped
 * across the whole run; it is dumped in [dumpExternalMethods] to `build/py-owasp-report/`
 * as a worklist for authoring pass-through approximations.
 *
 * Benchmark .py files are loaded from the owasp-benchmark-samples JAR (built by the samples
 * module). The JAR path is provided via the OWASP_BENCHMARK_SAMPLES_JAR environment variable
 * (set automatically by Gradle). The directory structure is preserved on extraction (only the
 * `owasp-benchmark/` prefix is stripped) and `searchPaths` points at the extraction root so
 * package imports (e.g. `testcode.BenchmarkTest00099`, `helpers.db_sqlite`) resolve.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class OwaspBenchmarkTest : AnalysisTest() {

    override val externalMethods = ExternalMethodTracker()

    override fun initCp(): PIRClasspath {
        val jarPath = System.getenv("OWASP_BENCHMARK_SAMPLES_JAR")
            ?: error("OWASP_BENCHMARK_SAMPLES_JAR environment variable not set. Run tests via Gradle.")

        sourcesDir = createTempDirectory("owasp-benchmark")
        extractPythonSources(Path(jarPath), sourcesDir)

        val pyFiles = sourcesDir.walk()
            .filter { it.isRegularFile() && it.extension == "py" }
            .mapTo(mutableListOf()) { it.absolutePathString() }

        return PIRClasspathLoader(
            PIRSettings(
                sources = pyFiles,
                mypyFlags = listOf(
                    "--ignore-missing-imports",
                    "--namespace-packages",
                    "--explicit-package-bases",
                ),
                searchPaths = listOf(sourcesDir.absolutePathString()),
                rpcTimeout = java.time.Duration.ofSeconds(1200),
            )
        ).load()
    }

    private fun extractPythonSources(jarPath: Path, targetDir: Path) {
        JarFile(jarPath.toFile()).use { jar ->
            jar.entries().asSequence()
                .filter { it.name.endsWith(".py") }
                .forEach { entry ->
                    val entryPath = Path(entry.name)
                    val relativeName = entryPath.subpath(1, entryPath.nameCount)
                    val targetFile = targetDir.resolve(relativeName)
                    targetFile.parent.createDirectories()
                    jar.getInputStream(entry).use { input ->
                        targetFile.writeText(input.bufferedReader().readText())
                    }
                }
        }
    }

    @AfterAll
    fun dumpExternalMethods() {
        val out = Path("build/py-owasp-report").also { it.createDirectories() }
        val ext = externalMethods.getExternalMethods()
        fun render(records: List<org.opentaint.dataflow.ap.ifds.taint.ExternalMethodRecord>) =
            records.joinToString("\n") {
                "${it.callSites.toString().padStart(4)}  ${it.method}  [${it.factPositions.joinToString(",")}]"
            } + "\n"
        out.resolve("external-methods-without-rules.txt").writeText(render(ext.withoutRules))
        out.resolve("external-methods-with-rules.txt").writeText(render(ext.withRules))
    }

    // ─── Per-entry assertions (ground truth hardcoded from expectedresults-0.1.csv) ───

    /**
     * Example entry: SQLi (CWE-89), `real vulnerability = true`. Request form data flows
     * through a configparser round-trip into an f-string SQL and reaches `cursor.execute`.
     * Establishes the shape the next session replicates per entry.
     */
    @Test
    fun benchmarkTest00099() = assertReachable("00099")

    // ─── SQLi seed set (CWE-89). true = execute(sql) interpolated; false = execute(sql, (param,)) ───

    @Test fun benchmarkTest00011() = assertNotReachable("00011")
    @Test fun benchmarkTest00012() = assertNotReachable("00012")
    @Test fun benchmarkTest00100() = assertNotReachable("00100")
    @Disabled("match/case unsupported in PIR (ast_serializer drops MatchStmt); module can't build")
    @Test fun benchmarkTest00192() = assertNotReachable("00192")
    @Test fun benchmarkTest00285() = assertNotReachable("00285")
    @Test fun benchmarkTest00286() = assertNotReachable("00286")
    @Disabled("match/case unsupported in PIR (ast_serializer drops MatchStmt); module can't build")
    @Test fun benchmarkTest00287() = assertNotReachable("00287")
    @Test fun benchmarkTest00755() = assertNotReachable("00755")
    @Test fun benchmarkTest01021() = assertNotReachable("01021")
    @Test fun benchmarkTest01203() = assertNotReachable("01203")
    @Test fun benchmarkTest01229() = assertNotReachable("01229")

    @Test fun benchmarkTest00283() = assertReachable("00283")
    @Test fun benchmarkTest00284() = assertReachable("00284")
    @Test fun benchmarkTest00454() = assertReachable("00454")
    @Test fun benchmarkTest00455() = assertReachable("00455")

    // ─── Plumbing ─────────────────────────────────────────────────────────────────

    private fun assertReachable(id: String) {
        val vulns = runAnalysis(rulesFor(id), entryFunction(id))
        assertTrue(vulns.isNotEmpty(), "[$id] sink was not reached")
    }

    private fun assertNotReachable(id: String) {
        val vulns = runAnalysis(rulesFor(id), entryFunction(id))
        assertTrue(vulns.isEmpty(), "[$id] sink should not be reached")
    }

    /** Layers the entry's hand-written semgrep rule over the pass-only shipped config. */
    private fun rulesFor(id: String): PIRTaintRulesProvider {
        val resource = "/owasp-benchmark-rules/BenchmarkTest$id.yaml"
        val yaml = javaClass.getResource(resource)?.readText()
            ?: error("Missing rule resource: $resource")
        val loader = SemgrepRuleLoader(listOf(PythonLanguageStrategy()))
        val trace = SemgrepLoadTrace()
        loader.registerRuleSet(yaml, Path("BenchmarkTest$id.yaml"), Path("."), trace)
        val rule = loader.loadRules().rulesWithMeta.firstOrNull()
            ?: error("No rules loaded from $resource; trace=${trace.compressed()}")

        @Suppress("UNCHECKED_CAST")
        val typed = rule.first as TaintRuleFromSemgrep<SerializedPythonRule>
        val ruleProvider = PIRConfigTaintRulesProvider(PIRTaintConfiguration(typed.toSerializedPythonTaintConfig()))

        // Default options: source/sink/entryPoint from the rule (OVERRIDE), passThrough/cleaner
        // extend the shipped pass-only base.
        return PIRCombinedTaintRulesProvider(loadDefaultConfig(), ruleProvider)
    }

    private fun entryFunction(id: String): String {
        require(id.length == 5 && id.all { it.isDigit() }) { "Invalid test id: $id" }
        return "testcode.BenchmarkTest$id.init\$BenchmarkTest${id}_post"
    }
}
