package org.opentaint.common.sast

import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.sarif.toolRunReport
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.project.CommonProject
import org.opentaint.semgrep.pattern.RuleMetadata
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

abstract class ProjectAnalyzer<
        Ctx : AutoCloseable,
        P : CommonProject,
        Method : CommonMethod,
        Stmt : CommonInst,
        RuleItem, RuleConfig
        >(
    project: P,
    results: ProjectAnalysisResults,
    options: CommonAnalysisOptions,
    private val loadedRules: SemgrepRuleLoader.RuleLoadResult,
) : ProjectAnalyzerBase<Ctx, P, Method, Stmt, RuleItem, RuleConfig, ProjectAnalysisResults>(
    project, results, options
) {
    private val ruleMetadatas = mutableListOf<RuleMetadata>()

    abstract fun initializeProjectAnalysisContext(): Ctx

    open fun analyze(): ProjectAnalysisStatus {
        if (loadedRules.noRuleSelected) {
            results.analysisSarifReport += project to
                options.sarifGenerationOptions.toolRunReport(project.sourceRoot(), emptyList(), emptySequence())
            return ProjectAnalysisStatus.OK
        }

        val rules = preloadRules()
        val projectAnalysisContext = initializeProjectAnalysisContext()

        return projectAnalysisContext.use {
            val entryPoints = it.selectProjectEntryPoints()
            it.runAnalyzer(entryPoints, rules)
        }
    }

    abstract fun Ctx.selectProjectEntryPoints(): List<Method>

    private fun preloadRules(): PreloadedRules<RuleItem, RuleConfig> {
        ruleMetadatas += loadedRules.rulesWithMeta.map { it.second }

        val rules = loadedRules.rulesWithMeta.map {
            @Suppress("UNCHECKED_CAST")
            it.first as TaintRuleFromSemgrep<RuleItem>
        }

        return preloadApproximation(rules)
    }

    private fun Ctx.runAnalyzer(
        entryPoints: List<Method>,
        rules: PreloadedRules<RuleItem, RuleConfig>
    ): ProjectAnalysisStatus {
        val externalMethodTracker = if (options.trackExternalMethods) ExternalMethodTracker() else null

        val analysisResult = runAnalyzerWithTraceResolver(entryPoints, rules, externalMethodTracker)
        generateReportFromAnalysisResult(analysisResult)

        if (externalMethodTracker != null) {
            val externalMethods = externalMethodTracker.getExternalMethods()
            writeExternalMethodsYaml(externalMethods)
        }

        return analysisResult.status.toProjectStatus()
    }

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
        return runAnalyzerWithTraceResolver(analyzer, entryPoints)
    }

    private fun Ctx.generateReportFromAnalysisResult(result: AnalysisResult) =
        generateReportFromAnalysisResult(result, ruleMetadatas)
}
