package org.opentaint.common.sast

import mu.KLogging
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.sarif.DebugFactReachabilitySarifGenerator
import org.opentaint.common.sast.sarif.LazyToolRunReport
import org.opentaint.common.sast.sarif.SarifGenerator
import org.opentaint.common.sast.util.asSequenceWithProgress
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.taint.SkippedExternalMethods
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.project.CommonProject
import org.opentaint.semgrep.pattern.RuleMetadata
import kotlin.time.Duration.Companion.seconds

abstract class ProjectAnalyzerBase<
        Ctx : AutoCloseable,
        P : CommonProject,
        Method : CommonMethod,
        Stmt : CommonInst,
        RuleItem, RuleConfig,
        Res : ProjectAnalysisResults
        >(
    val project: P,
    val results: Res,
    val options: CommonAnalysisOptions,
) {
    data class AnalysisResult(
        val status: TaintAnalyzer.Status,
        val traces: List<VulnerabilityWithTrace>,
        val seVerifiedTraces: List<VulnerabilityWithTrace>? = null,
        val debugStatementsWithFact: Map<CommonInst, Set<FinalFactAp>>? = null
    )

    fun Ctx.runAnalyzerWithTraceResolver(
        analyzer: TaintAnalyzer<Method, Stmt>,
        entryPoints: List<Method>
    ): AnalysisResult = analyzer.use { analyzer ->
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

    abstract fun Ctx.runSeAnalyzer(
        engine: TaintAnalysisUnitRunnerManager,
        traces: List<VulnerabilityWithTrace>
    ): List<VulnerabilityWithTrace>

    fun Ctx.generateReportFromAnalysisResult(result: AnalysisResult, ruleMetadata: List<RuleMetadata>) {
        logger.info { "Start SARIF report generation for project: ${project.sourceRoot()}" }

        results.analysisSarifReport += project to generateSarifReportFromTraces(result.traces, ruleMetadata)

        result.debugStatementsWithFact?.let { stmtsWithFact ->
            results.factReachabilityReport += project to generateFactReachabilityReport(stmtsWithFact)
        }

        result.seVerifiedTraces?.let { seVerifiedTraces ->
            results.seVerifiedSarifReport += project to generateSarifReportFromTraces(seVerifiedTraces, ruleMetadata)
        }

        logger.info { "Finish SARIF report for project: ${project.sourceRoot()}" }
    }

    abstract fun Ctx.sarifGenerator(): SarifGenerator<*>

    fun Ctx.generateSarifReportFromTraces(
        traces: List<VulnerabilityWithTrace>,
        ruleMetadata: List<RuleMetadata>,
    ): LazyToolRunReport {
        val generator = sarifGenerator()

        val tracesWithProgress = traces.asSequenceWithProgress(10.seconds) { taken, overall ->
            logger.info { "Generated ${taken - 1}/${overall} sarif traces" }
        }

        return generator.generateSarif(tracesWithProgress, ruleMetadata).also {
            logger.info { "Sarif trace generation stats: ${generator.traceGenerationStats}" }
        }
    }

    abstract fun Ctx.debugSarifGenerator(): DebugFactReachabilitySarifGenerator<*>

    fun Ctx.generateFactReachabilityReport(
        reachableFacts: Map<CommonInst, Set<FinalFactAp>>,
    ): LazyToolRunReport {
        val generator = debugSarifGenerator()
        return generator.generateSarif(reachableFacts)
    }

    fun writeExternalMethodsYaml(extMethods: SkippedExternalMethods) {
        logger.info { "Dropped external methods (${extMethods.withoutRules.size} entries)" }
        logger.info { "Approximated external methods (${extMethods.withRules.size} entries)" }
        results.externalMethodsWithoutRules += project to extMethods
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
