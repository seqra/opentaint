package org.opentaint.go.sast.project

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.encodeToStream
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.SkippedExternalMethods
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.rules.GoCombinedTaintRulesProvider
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.go.config.GoConfigLoader
import org.opentaint.go.config.loadGoSerializedTaintConfig
import org.opentaint.go.sast.dataflow.GoTaintAnalyzer
import org.opentaint.go.sast.dataflow.GoUnitResolver
import org.opentaint.go.sast.sarif.GoSarifGenerator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.jvm.sast.project.ProjectAnalysisStatus
import org.opentaint.jvm.sast.project.rules.loadSemgrepRules
import org.opentaint.project.GoProject
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toGoSerializedTaintConfig
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.inputStream
import kotlin.io.path.outputStream

class GoProjectAnalyzer(
    private val project: GoProject,
    private val resultDir: Path,
    private val options: GoProjectAnalysisOptions = GoProjectAnalysisOptions(),
) {
    fun analyze(): ProjectAnalysisStatus = try {
        GoIRClient().use { client ->
            logger.info { "Building Go IR for project: ${project.projectDir}" }
            val cp = client.buildFromDir(project.projectDir, "./...")

            val rulesProvider = loadRules()
            val tracker = if (options.common.trackExternalMethods) ExternalMethodTracker() else null

            val analyzer = GoTaintAnalyzer(
                cp = cp,
                taintConfig = rulesProvider,
                unitResolver = GoUnitResolver(),
                externalMethodTracker = tracker,
                analysisTimeout = options.common.ifdsAnalysisTimeout,
            )
            val entryPoints = selectEntryPoints(cp)
            logger.info { "Selected ${entryPoints.size} Go entry points" }

            val traces = analyzer.analyzeWithIfds(entryPoints)
            logger.info { "Go analysis produced ${traces.size} traces" }

            writeReport(traces)
            tracker?.let { writeExternalMethodsYaml(it.getExternalMethods()) }
        }
        ProjectAnalysisStatus.OK
    } catch (ex: Throwable) {
        logger.error(ex) { "Go analysis failed for project: ${project.projectDir}" }
        ProjectAnalysisStatus.EXCEPTION
    }

    private fun loadRules(): GoTaintRulesProvider {
        val userConfig = GoTaintConfiguration()

        GoConfigLoader.getConfig()?.let { userConfig.loadConfig(it) }

        val semgrepRules = options.common.loadSemgrepRules(GoLanguageStrategy())
        for ((rule, _) in semgrepRules.rulesWithMeta) {
            @Suppress("UNCHECKED_CAST")
            val typed = rule as TaintRuleFromSemgrep<GoSerializedItem>
            userConfig.loadConfig(typed.toGoSerializedTaintConfig())
        }

        if (options.common.customApproximationConfig.isEmpty()) return userConfig

        val approxConfig = GoTaintConfiguration()
        options.common.customApproximationConfig.forEach { cfg ->
            cfg.inputStream().use { approxConfig.loadConfig(loadGoSerializedTaintConfig(it)) }
        }
        return GoCombinedTaintRulesProvider(userConfig, approxConfig)
    }

    private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
        cp.packages.values
            .filter { it.isProject }
            .flatMap { it.functions }
            .filter { it.hasBody && !it.isSynthetic && it.parent == null }

    private fun writeReport(traces: List<VulnerabilityWithTrace>) {
        val sarif = options.common.sarifGenerationOptions
        val generator = GoSarifGenerator(sarif, project.projectDir)
        (resultDir / sarif.sarifFileName).outputStream().use { out ->
            generator.generateSarif(out, traces.asSequence())
        }
        logger.info { "Wrote Go SARIF report to ${resultDir / sarif.sarifFileName}" }
    }

    private fun writeExternalMethodsYaml(methods: SkippedExternalMethods) {
        val yaml = Yaml(configuration = YamlConfiguration(encodeDefaults = true))
        (resultDir / "external-methods-without-rules.yaml").outputStream().use {
            yaml.encodeToStream(methods.withoutRules, it)
        }
        (resultDir / "external-methods-with-rules.yaml").outputStream().use {
            yaml.encodeToStream(methods.withRules, it)
        }
        logger.info {
            "Wrote external-methods YAMLs (${methods.withoutRules.size} without rules, " +
                "${methods.withRules.size} with rules)"
        }
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
