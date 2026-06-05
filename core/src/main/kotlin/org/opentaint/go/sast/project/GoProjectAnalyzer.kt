package org.opentaint.go.sast.project

import mu.KLogging
import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.ProjectAnalyzer
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.go.rules.GoCombinedTaintRulesProvider
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.go.config.GoConfigLoader
import org.opentaint.go.config.loadGoSerializedTaintConfig
import org.opentaint.go.sast.dataflow.GoTaintAnalyzer
import org.opentaint.go.sast.dataflow.GoUnitResolver
import org.opentaint.go.sast.project.GoProjectAnalyzer.AnalysisCtx
import org.opentaint.go.sast.sarif.GoDebugFactReachabilitySarifGenerator
import org.opentaint.go.sast.sarif.GoSarifGenerator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.client.GoIRLoadMode
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.project.GoProject
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toGoSerializedTaintConfig
import java.io.InputStream
import java.nio.file.Path

class GoProjectAnalyzer(
    project: GoProject,
    resultDir: Path,
    goOptions: GoProjectAnalysisOptions = GoProjectAnalysisOptions(),
) : ProjectAnalyzer<AnalysisCtx, GoProject, GoIRFunction, GoIRInst, GoSerializedItem, GoSerializedTaintConfig>(
    project,
    resultDir,
    goOptions.common
) {
    class AnalysisCtx(
        private val prj: GoProject,
        val client: GoIRClient,
    ) : AutoCloseable by client {
        val cp: GoIRProgram by lazy {
            logger.info { "Building Go IR for project: ${prj.projectDir}" }
            client.buildFromDir(prj.projectDir, GoIRLoadConfig(mode = GoIRLoadMode.PROJECT)).program
        }
    }

    override fun initializeProjectAnalysisContext(): AnalysisCtx {
        val client = GoIRClient()
        return AnalysisCtx(project, client)
    }

    override fun AnalysisCtx.selectProjectEntryPoints(): List<GoIRFunction> {
        val all = cp.packages.values
            .filter { it.isProject }
            .flatMap { it.functions }
            .filter { it.hasBody && !it.isSynthetic && it.parent == null }

        val selector = options.debugOptions?.debugRunAnalysisOnSelectedEntryPoints
        val filtered = filterEntryPoints(all, selector)
        if (selector != null && selector != "*" && filtered.isEmpty()) {
            logger.warn { "Entry-point selector matched no project function: '$selector'" }
        }
        return filtered
    }

    override fun ruleStrategy() = GoLanguageStrategy()

    override fun loadApproximationConfig(stream: InputStream): GoSerializedTaintConfig =
        loadGoSerializedTaintConfig(stream)

    override fun AnalysisCtx.createAnalyzer(
        externalMethodTracker: ExternalMethodTracker?,
        rules: PreloadedRules<GoSerializedItem, GoSerializedTaintConfig>
    ): TaintAnalyzer<GoIRFunction, GoIRInst> {
        val rulesProvider = loadRules(rules)
        return GoTaintAnalyzer(
            cp,
            rulesProvider,
            GoUnitResolver(),
            options.taintAnalyzerOptions(),
            externalMethodTracker
        )
    }

    override fun AnalysisCtx.sarifGenerator() =
        GoSarifGenerator(options.sarifGenerationOptions, project.sourceRoot())

    override fun AnalysisCtx.debugSarifGenerator() =
        GoDebugFactReachabilitySarifGenerator(options.sarifGenerationOptions, project.sourceRoot())

    override fun AnalysisCtx.runSeAnalyzer(
        engine: TaintAnalysisUnitRunnerManager,
        traces: List<VulnerabilityWithTrace>
    ): List<VulnerabilityWithTrace> {
        TODO("Not yet implemented")
    }

    private fun loadRules(rules: PreloadedRules<GoSerializedItem, GoSerializedTaintConfig>): GoTaintRulesProvider {
        val userConfig = GoTaintConfiguration()
        GoConfigLoader.getConfig()?.let { userConfig.loadConfig(it) }

        rules.rules.forEach {
            userConfig.loadConfig(it.toGoSerializedTaintConfig())
        }

        if (rules.customApproximationConfig.isEmpty()) return userConfig

        val approxConfig = GoTaintConfiguration()
        rules.customApproximationConfig.forEach { approxConfig.loadConfig(it) }
        return GoCombinedTaintRulesProvider(userConfig, approxConfig)
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}

internal fun filterEntryPoints(
    entryPoints: List<GoIRFunction>,
    selector: String?,
): List<GoIRFunction> {
    if (selector == null || selector == "*") return entryPoints
    return entryPoints.filter { it.fullName == selector }
}
