package org.opentaint.jvm.sast.project

import org.opentaint.common.sast.ProjectAnalyzer
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.loadSerializedTaintConfig
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.sast.dataflow.JIRTaintAnalyzer
import org.opentaint.jvm.sast.dataflow.JIRTaintRulesProvider
import org.opentaint.jvm.sast.dataflow.rules.TaintConfiguration
import org.opentaint.jvm.sast.project.rules.analysisConfig
import org.opentaint.jvm.sast.project.rules.withApproximationConfigs
import org.opentaint.jvm.sast.sarif.JIRSarifTraits
import org.opentaint.jvm.sast.sarif.JirDebugFactReachabilitySarifGenerator
import org.opentaint.jvm.sast.sarif.JirSarifGenerator
import org.opentaint.jvm.sast.se.api.SastSeAnalyzer
import org.opentaint.jvm.sast.util.loadDefaultConfig
import org.opentaint.jvm.sast.util.locationChecker
import org.opentaint.project.JavaProject
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.createTaintConfig
import java.io.InputStream
import java.nio.file.Path

class JirProjectAnalyzer(
    project: JavaProject,
    resultDir: Path,
    private val jirOptions: ProjectAnalysisOptions,
): ProjectAnalyzer<ProjectAnalysisContext, JavaProject, JIRMethod, JIRInst, SerializedItem, SerializedTaintConfig>(
    project, resultDir, jirOptions.common
) {
    override fun initializeProjectAnalysisContext() =
        initializeProjectAnalysisContext(project, jirOptions)

    override fun ProjectAnalysisContext.selectProjectEntryPoints() =
        selectProjectEntryPoints(jirOptions)

    override fun ruleStrategy() = JavaLanguageStrategy()

    override fun loadApproximationConfig(stream: InputStream) = loadSerializedTaintConfig(stream)

    private fun loadTaintConfig(cp: JIRClasspath, rules: PreloadedRules<SerializedItem, SerializedTaintConfig>): TaintRulesProvider {
        val config = TaintConfiguration(cp)
        rules.rules.forEach { config.loadConfig(it.createTaintConfig()) }

        val defaultPassRules = loadDefaultConfig()
        config.loadConfig(defaultPassRules)

        return JIRTaintRulesProvider(config).withApproximationConfigs(cp, rules.customApproximationConfig)
    }

    override fun ProjectAnalysisContext.createAnalyzer(
        externalMethodTracker: ExternalMethodTracker?,
        rules: PreloadedRules<SerializedItem, SerializedTaintConfig>
    ): TaintAnalyzer<JIRMethod, JIRInst> {
        val loadedConfig = loadTaintConfig(cp, rules)
        val config = analysisConfig(loadedConfig)
        return JIRTaintAnalyzer(
            cp, config,
            projectClasses = projectClasses.locationChecker(),
            options = options.taintAnalyzerOptions(),
            externalMethodTracker = externalMethodTracker,
        )
    }

    override fun ProjectAnalysisContext.runSeAnalyzer(
        engine: TaintAnalysisUnitRunnerManager,
        traces: List<VulnerabilityWithTrace>
    ): List<VulnerabilityWithTrace> {
        val seAnalyzer = SastSeAnalyzer.createSeEngine<TaintAnalysisUnitRunnerManager, VulnerabilityWithTrace>()
            ?: return traces

        val seOptions = SastSeAnalyzer.SeOptions(
            options.symbolicExecutionTimeout, options.experimentalAAInterProcCallDepth
        )
        return seAnalyzer.analyzeTraces(
            cp, projectClasses.projectLocationsUnsafe, engine,
            traces, seOptions
        )
    }

    override fun ProjectAnalysisContext.sarifGenerator(): SarifGenerator<*> {
        val sourcesResolver = project.sourceResolver(projectClasses)
        return JirSarifGenerator(
            options.sarifGenerationOptions, project.sourceRoot,
            sourcesResolver, JIRSarifTraits(cp)
        )
    }

    override fun ProjectAnalysisContext.debugSarifGenerator(): DebugFactReachabilitySarifGenerator<*> {
        val sourcesResolver = project.sourceResolver(projectClasses)
        return JirDebugFactReachabilitySarifGenerator(
            options.sarifGenerationOptions,
            sourcesResolver, JIRSarifTraits(cp)
        )
    }
}
