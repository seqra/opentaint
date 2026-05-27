package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
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
import kotlin.test.Test

/**
 * Runs the OWASP Benchmark for Python.
 *
 * Benchmark .py files are loaded from the owasp-benchmark-samples JAR (built by the samples
 * module). The JAR path is provided via the OWASP_BENCHMARK_SAMPLES_JAR environment variable
 * (set automatically by Gradle).
 *
 * Unlike the Ant benchmark, the OWASP benchmark relies on package imports
 * (e.g. `testcode.BenchmarkTest00283`, `helpers.db_sqlite`), so the directory structure is
 * preserved on extraction (only the `owasp-benchmark/` prefix is stripped) and `searchPaths`
 * points at the extraction root so those imports resolve.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class OwaspBenchmarkTest : AnalysisTest() {

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

    /**
     * Extracts every .py entry from the benchmark JAR, preserving its relative path below the
     * top-level benchmark directory, so that `testcode/...`, `helpers/...` and `app.py` land
     * at [targetDir] and module imports resolve.
     */
    private fun extractPythonSources(jarPath: Path, targetDir: Path) {
        JarFile(jarPath.toFile()).use { jar ->
            jar.entries().asSequence()
                .filter { it.name.endsWith(".py") }
                .forEach { entry ->
                    // Drop the leading benchmark-root segment (e.g. "owasp-benchmark/").
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

    @Test
    fun sqlInjection() {
        assertSinkNotReachable("testcode.BenchmarkTest00283.init\$BenchmarkTest00283_post")
    }
}
