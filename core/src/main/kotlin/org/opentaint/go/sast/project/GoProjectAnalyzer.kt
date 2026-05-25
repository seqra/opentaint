package org.opentaint.go.sast.project

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.go.rules.GoTaintConfig
import org.opentaint.go.sast.dataflow.GoTaintAnalyzer
import org.opentaint.go.sast.dataflow.GoUnitResolver
import org.opentaint.go.sast.sarif.GoSarifGenerator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.jvm.sast.project.SarifGenerationOptions
import org.opentaint.project.GoProject
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.outputStream

/**
 * Go counterpart of [org.opentaint.jvm.sast.project.ProjectAnalyzer].
 *
 * Builds a [GoIRProgram] from a [GoProject] via [GoIRClient], runs the Go taint
 * analyzer with the predefined stub rules over the project's own functions, and
 * writes a SARIF report into [resultDir]. Rule loading is intentionally omitted.
 */
class GoProjectAnalyzer(
    private val project: GoProject,
    private val resultDir: Path,
    private val options: SarifGenerationOptions = SarifGenerationOptions(),
) {
    fun analyze() {
        GoIRClient().use { client ->
            logger.info { "Building Go IR for project: ${project.projectDir}" }
            val cp = client.buildFromDir(project.projectDir, "./...")

            val projectImportPaths = cp.packages.keys.toSet()
            val entryPoints = selectEntryPoints(cp)
            logger.info { "Selected ${entryPoints.size} Go entry points" }

            val analyzer = GoTaintAnalyzer(
                cp = cp,
                taintConfig = loadRules(),
                unitResolver = GoUnitResolver(projectImportPaths),
            )
            val traces = analyzer.analyzeWithIfds(entryPoints)
            logger.info { "Go analysis produced ${traces.size} traces" }

            writeReport(traces)
        }
    }

    private fun loadRules(): GoTaintConfig = TODO()

    private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
        cp.allFunctions().filter { it.hasBody && it.pkg != null && !it.isSynthetic && it.parent == null }

    private fun writeReport(traces: List<VulnerabilityWithTrace>) {
        val generator = GoSarifGenerator(options, project.projectDir)
        (resultDir / options.sarifFileName).outputStream().use { out ->
            generator.generateSarif(out, traces.asSequence())
        }
        logger.info { "Wrote Go SARIF report to ${resultDir / options.sarifFileName}" }
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
