package org.opentaint.common.sast

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.encodeToStream
import mu.KLogging
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.rules.loadSemgrepRules
import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.util.asSequenceWithProgress
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.SkippedExternalMethods
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.project.CommonProject
import org.opentaint.semgrep.pattern.RuleMetadata
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import java.io.InputStream
import java.io.OutputStream
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.inputStream
import kotlin.io.path.outputStream
import kotlin.time.Duration.Companion.seconds

abstract class ProjectAnalyzer<
        Ctx : AutoCloseable,
        P : CommonProject,
        Method : CommonMethod,
        Stmt : CommonInst,
        RuleItem, RuleConfig
        >(
    val project: P,
    val resultDir: Path,
    val options: CommonAnalysisOptions,
) {
    private val ruleMetadatas = mutableListOf<RuleMetadata>()

    abstract fun initializeProjectAnalysisContext(): Ctx

    fun analyze(): ProjectAnalysisStatus {
        val rules = preloadRules()
        val projectAnalysisContext = initializeProjectAnalysisContext()

        return projectAnalysisContext.use {
            val entryPoints = it.selectProjectEntryPoints()
            it.runAnalyzer(entryPoints, rules)
        }
    }

    abstract fun Ctx.selectProjectEntryPoints(): List<Method>

    data class PreloadedRules<RuleItem, RuleConfig>(
        val rules: List<TaintRuleFromSemgrep<RuleItem>>,
        val customApproximationConfig: List<RuleConfig>,
    )

    abstract fun ruleStrategy(): LanguageStrategy<*, RuleItem>

    abstract fun loadApproximationConfig(stream: InputStream): RuleConfig

    private fun preloadRules(): PreloadedRules<RuleItem, RuleConfig> {
        val loadedRules = options.loadSemgrepRules(ruleStrategy())
        ruleMetadatas += loadedRules.rulesWithMeta.map { it.second }

        val rules = loadedRules.rulesWithMeta.map {
            @Suppress("UNCHECKED_CAST")
            it.first as TaintRuleFromSemgrep<RuleItem>
        }

        val approximations = options.customApproximationConfig.map { cfg ->
            cfg.inputStream().use { cfgStream ->
                loadApproximationConfig(cfgStream)
            }
        }

        return PreloadedRules(rules, approximations)
    }

    private fun Ctx.runAnalyzer(entryPoints: List<Method>, rules: PreloadedRules<RuleItem, RuleConfig>): ProjectAnalysisStatus {
        val externalMethodTracker = if (options.trackExternalMethods) ExternalMethodTracker() else null

        val analysisResult = runAnalyzerWithTraceResolver(entryPoints, rules, externalMethodTracker)
        generateReportFromAnalysisResult(analysisResult)

        if (externalMethodTracker != null) {
            val externalMethods = externalMethodTracker.getExternalMethods()
            writeExternalMethodsYaml(externalMethods)
        }

        return analysisResult.status.toProjectStatus()
    }

    private data class AnalysisResult(
        val status: TaintAnalyzer.Status,
        val traces: List<VulnerabilityWithTrace>,
        val seVerifiedTraces: List<VulnerabilityWithTrace>? = null,
        val debugStatementsWithFact: Map<CommonInst, Set<FinalFactAp>>? = null
    )

    abstract fun Ctx.createAnalyzer(
        externalMethodTracker: ExternalMethodTracker?,
        rules: PreloadedRules<RuleItem, RuleConfig>,
    ): TaintAnalyzer<Method, Stmt>

    private fun Ctx.runAnalyzerWithTraceResolver(
        entryPoints: List<Method>,
        rules: PreloadedRules<RuleItem, RuleConfig>,
        externalMethodTracker: ExternalMethodTracker? = null,
    ): AnalysisResult {
        val analyzer = createAnalyzer(externalMethodTracker, rules)
        analyzer.use { analyzer ->
            logger.info { "Start IFDS analysis for project: ${project.sourceRoot()}" }
            val (traces, status) = analyzer.analyzeWithIfds(entryPoints)
            logger.info { "Finish IFDS analysis for project: ${project.sourceRoot()}" }

            var result = AnalysisResult(status, traces)

            if (options.debugOptions?.factReachabilitySarif == true) {
                val stmtsWithFact = analyzer.statementsWithFacts()
                result = result.copy(debugStatementsWithFact = stmtsWithFact)
            }

            if (!options.useSymbolicExecution) return result

            logger.info { "Start SE for project: ${project.sourceRoot()}" }

            val verifiedTraces = runSeAnalyzer(analyzer.ifdsEngine, traces)
            logger.info { "Finish SE for project: ${project.sourceRoot()}" }

            result = result.copy(seVerifiedTraces = verifiedTraces)

            return result
        }
    }

    abstract fun Ctx.runSeAnalyzer(
        engine: TaintAnalysisUnitRunnerManager,
        traces: List<VulnerabilityWithTrace>
    ): List<VulnerabilityWithTrace>

    private fun Ctx.generateReportFromAnalysisResult(result: AnalysisResult) {
        logger.info { "Start SARIF report generation for project: ${project.sourceRoot()}" }

        (resultDir / options.sarifGenerationOptions.sarifFileName).outputStream().use {
            generateSarifReportFromTraces(it, result.traces)
        }

        result.debugStatementsWithFact?.let { stmtsWithFact ->
            (resultDir / "debug-ifds-fact-reachability.sarif").outputStream().use {
                generateFactReachabilityReport(it, stmtsWithFact)
            }
        }

        result.seVerifiedTraces?.let { seVerifiedTraces ->
            val reportName = options.sarifGenerationOptions.sarifFileName + ".se-verified.sarif"
            (resultDir / reportName).outputStream().use {
                generateSarifReportFromTraces(it, seVerifiedTraces)
            }
        }

        logger.info { "Finish SARIF report for project: ${project.sourceRoot()}" }
    }

    abstract fun Ctx.sarifGenerator(): SarifGenerator<*>

    private fun Ctx.generateSarifReportFromTraces(
        output: OutputStream,
        traces: List<VulnerabilityWithTrace>
    ) {
        val generator = sarifGenerator()

        val tracesWithProgress = traces.asSequenceWithProgress(10.seconds) { taken, overall ->
            logger.info { "Generated ${taken - 1}/${overall} sarif traces" }
        }

        generator.generateSarif(output, tracesWithProgress, ruleMetadatas)
        logger.info { "Sarif trace generation stats: ${generator.traceGenerationStats}" }
    }

    abstract fun Ctx.debugSarifGenerator(): DebugFactReachabilitySarifGenerator<*>

    private fun Ctx.generateFactReachabilityReport(
        output: OutputStream,
        reachableFacts: Map<CommonInst, Set<FinalFactAp>>,
    ) {
        val generator = debugSarifGenerator()
        generator.generateSarif(output, reachableFacts)
    }

    private fun writeExternalMethodsYaml(extMethods: SkippedExternalMethods) {
        val droppedPath = resultDir / DROPPED_EXTERNAL_METHODS_FILE_NAME
        val approximatedPath = resultDir / APPROXIMATED_EXTERNAL_METHODS_FILE_NAME

        droppedPath.outputStream().use { stream ->
            skippedMethodsYaml.encodeToStream(extMethods.withoutRules, stream)
        }

        logger.info { "Wrote dropped external methods to $droppedPath (${extMethods.withoutRules.size} entries)" }

        approximatedPath.outputStream().use { stream ->
            skippedMethodsYaml.encodeToStream(extMethods.withRules, stream)
        }

        logger.info { "Wrote approximated external methods to $approximatedPath (${extMethods.withRules.size} entries)" }
    }

    companion object {
        private val logger = object : KLogging() {}.logger

        const val DROPPED_EXTERNAL_METHODS_FILE_NAME = "dropped-external-methods.yaml"
        const val APPROXIMATED_EXTERNAL_METHODS_FILE_NAME = "approximated-external-methods.yaml"

        private val skippedMethodsYaml = Yaml(
            configuration = YamlConfiguration(encodeDefaults = true)
        )
    }
}
