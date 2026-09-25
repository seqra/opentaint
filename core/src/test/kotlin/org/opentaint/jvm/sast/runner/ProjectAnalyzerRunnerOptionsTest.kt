package org.opentaint.jvm.sast.runner

import com.github.ajalt.clikt.parsers.CommandLineParser
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import java.nio.file.Files
import kotlin.io.path.createTempDirectory
import kotlin.io.path.deleteRecursively
import kotlin.io.path.ExperimentalPathApi
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/** The mark-set CLI options reach [MarkSetScanOptions] (spec §10). The command is parsed, not run. */
@OptIn(ExperimentalPathApi::class)
class ProjectAnalyzerRunnerOptionsTest {
    private fun markSetOptions(vararg flags: String): MarkSetScanOptions {
        val dir = createTempDirectory("runner-options")
        try {
            val project = Files.createFile(dir.resolve("project.yaml"))
            val runner = ProjectAnalyzerRunner()
            val args = listOf("--project", project.toString(), "--output-dir", dir.resolve("out").toString()) + flags
            CommandLineParser.parseAndRun(runner, args) {}
            return runner.commonOptions().markSet
        } finally {
            dir.deleteRecursively()
        }
    }

    @Test
    fun `the mark-set scan is on by default, with no flags`() {
        assertEquals(MarkSetScanOptions(), markSetOptions())
        assertTrue(markSetOptions().enabled, "the mark-set scan is off with no flags")
    }

    @Test
    fun `--no-mark-set-scan turns the default-on mark-set scan off`() {
        assertEquals(MarkSetScanOptions(enabled = false), markSetOptions("--no-mark-set-scan"))
    }

    @Test
    fun `the mark-set sub-flags are still parsed alongside the default-on scan`() {
        assertEquals(
            MarkSetScanOptions(enabled = true, relaxed = true),
            markSetOptions("--mark-set-relaxed"),
        )
        assertEquals(
            MarkSetScanOptions(enabled = true, relevance = false),
            markSetOptions("--mark-set-no-relevance"),
        )
        assertEquals(
            MarkSetScanOptions(enabled = true, flowSensitive = true),
            markSetOptions("--mark-set-flow-sensitive"),
        )
    }

    @Test
    fun `the hidden debug-check flag turns on the mark-set debug checks`() {
        assertEquals(
            MarkSetScanOptions(enabled = true, debugChecks = true),
            markSetOptions("--mark-set-debug-checks"),
        )
    }
}
