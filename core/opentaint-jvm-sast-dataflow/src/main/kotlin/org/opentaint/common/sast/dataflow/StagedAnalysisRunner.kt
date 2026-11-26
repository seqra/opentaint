package org.opentaint.common.sast.dataflow

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.ExactProcessingTimeBudget
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.ap.ifds.trace.action.ActionableRulesCollectionResult
import org.opentaint.dataflow.ap.ifds.trace.action.mergeActionableRules
import org.opentaint.dataflow.ap.ifds.trace.path.TracePathGenerationResult
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.ir.api.common.CommonMethod
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlin.time.TimeMark
import kotlin.time.TimeSource

internal class StagedAnalysisRunner<Method : CommonMethod>(
    private val options: TaintAnalyzerOptions,
    private val analysisManager: TaintAnalysisManager,
    private val engine: TaintAnalysisUnitRunnerManager,
    private val prescanApManager: ApManager,
    private val finalApManager: ApManager,
    private val createShallowApManager: () -> ApManager,
    private val coverageReport: () -> String,
    private val vulnerabilitySummary: (List<TaintSinkTracker.TaintVulnerability>) -> String,
    private val generateTraces: (
        List<Method>,
        List<TaintSinkTracker.TaintVulnerability>,
        Duration,
    ) -> List<VulnerabilityWithTrace>,
) {
    fun analyze(entryPoints: List<Method>): Pair<List<VulnerabilityWithTrace>, TaintAnalyzer.Status> {
        val analysisStart = TimeSource.Monotonic.markNow()
        val startMethods = entryPoints.map { MethodWithContext(it, EmptyMethodContext) }

        logger.info { "Start prescan phase" }
        prescan(startMethods)
        logger.info { "Finish prescan phase" }

        logger.info { "Start shallow scan phase" }
        val actionableRules = shallowScan(analysisStart, entryPoints, startMethods)
        logger.info { "Finish shallow scan phase" }

        logger.info { "Start full scan phase" }
        val result = fullScan(analysisStart, entryPoints, startMethods, actionableRules)
        logger.info { "Finish full scan phase" }
        return result
    }

    private fun prescan(startMethods: List<MethodWithContext>) {
        analysisManager.selectPhase(TaintAnalysisManager.Phase.Prescan)
        engine.resetApManager(prescanApManager)
        runCatching {
            engine.runAnalysis(
                startMethods,
                timeout = options.ifdsTimeout * 0.30,
                cancellationTimeout = 30.seconds,
            )
        }.onFailure { logger.error(it) { "Prescan failed" } }
        if (options.debugOptions?.enableIfdsCoverage == true) logger.debug(coverageReport)
        engine.cleanup()
    }

    /** Null means discovery was incomplete, so the full scan must retain method-level selection. */
    private fun shallowScan(
        analysisStart: TimeMark,
        entryPoints: List<Method>,
        startMethods: List<MethodWithContext>,
    ): ActionableRules? {
        if (startMethods.size > options.shallowScanMethodLimit) {
            return failOpen(
                "Shallow analysis entry surface ${startMethods.size} exceeds " +
                    "the ${options.shallowScanMethodLimit}-method budget",
            )
        }
        val shallowApManager = createShallowApManager()
        analysisManager.selectPhase(TaintAnalysisManager.Phase.ShallowScan)
        engine.resetApManager(shallowApManager)
        val shallowTimeout = minOf(
            options.shallowScanTimeLimit,
            (options.ifdsTimeout - analysisStart.elapsedNow()) * 0.40,
        )
        if (!shallowTimeout.isPositive()) return failOpen("No time remains for shallow analysis")
        val completed = runCatching {
            engine.runAnalysis(
                startMethods,
                timeout = shallowTimeout,
                cancellationTimeout = 30.seconds,
            )
        }.onFailure { logger.error(it) { "Shallow analysis failed" } }.isSuccess
        engine.cleanup()
        if (!completed || engine.status.get() != TaintAnalysisUnitRunnerManager.Status.OK) {
            logger.warn { "Shallow scan was incomplete; full scan will use prescan-selected rules" }
            return null
        }

        val confirmationTimeout = options.ifdsTimeout - analysisStart.elapsedNow()
        if (!confirmationTimeout.isPositive()) return failOpen("No time remains for shallow confirmation")
        val vulnerabilities = engine.confirmVulnerabilities(
            entryPoints.toHashSet(),
            engine.getVulnerabilities(),
            confirmationTimeout,
            cancellationTimeout = 30.seconds,
        )
        if (engine.status.get() != TaintAnalysisUnitRunnerManager.Status.OK || vulnerabilities.isEmpty()) {
            return failOpen("Shallow confirmation produced no complete selection")
        }

        val searchTimeout = (options.ifdsTimeout - analysisStart.elapsedNow()) * 0.50
        if (!searchTimeout.isPositive()) return failOpen("No time remains for exact rule search")
        val exactBudget = ExactProcessingTimeBudget<TaintSinkTracker.TaintVulnerability>(
            options.shallowRuleSearchExactTimeLimit,
        )
        (shallowApManager as? BaseOnlyApManager)?.enableTraceResolutionMode()
        val traces = engine.resolveVulnerabilityInterProceduralTraces(
            entryPoints.toHashSet(),
            vulnerabilities,
            resolverParams = TraceResolver.Params(
                resolveEntryPointToStartTrace = false,
                resolveAllTraces = true,
            ),
            timeout = searchTimeout * 0.50,
            cancellationTimeout = 30.seconds,
            exactTimeBudget = exactBudget,
        )
        val results = engine.resolveVulnerabilityActionableRules(
            traces,
            timeout = searchTimeout * 0.50,
            cancellationTimeout = 30.seconds,
            exactTimeBudget = exactBudget,
        )
        if (results.size != vulnerabilities.size ||
            results.any { it !is ActionableRulesCollectionResult.Collected }
        ) {
            return failOpen("Exact rule search was incomplete")
        }

        val selection = mergeActionableRules(
            results.filterIsInstance<ActionableRulesCollectionResult.Collected>(),
        ).takeIf { it.isNotEmpty() } ?: return failOpen("Exact rule search selected no rules")
        val sources = selection.values.sumOf { rules -> rules.count { it.value.isNotEmpty() } }
        val sinks = selection.values.sumOf { rules -> rules.count { it.value.isEmpty() } }
        logger.info { "Shallow selection retained $sources source rules and $sinks sink rules" }
        return selection
    }

    private fun failOpen(reason: String): ActionableRules? {
        logger.warn { "$reason; full scan will use prescan-selected rules" }
        return null
    }

    private fun fullScan(
        analysisStart: TimeMark,
        entryPoints: List<Method>,
        startMethods: List<MethodWithContext>,
        actionableRules: ActionableRules?,
    ): Pair<List<VulnerabilityWithTrace>, TaintAnalyzer.Status> {
        analysisManager.selectPhase(TaintAnalysisManager.Phase.FullScan(actionableRules))
        engine.resetApManager(finalApManager)
        runCatching {
            engine.runAnalysis(
                startMethods,
                timeout = (options.ifdsTimeout - analysisStart.elapsedNow()) * 0.80,
                cancellationTimeout = 30.seconds,
            )
        }.onFailure { logger.error(it) { "Full analysis failed" } }
        val analysisStatus = engine.status.get()

        if (options.storeSummaries) {
            logger.info { "Storing summaries" }
            engine.storeSummaries()
        }
        engine.cleanup()

        val confirmationTimeout = options.ifdsTimeout - analysisStart.elapsedNow()
        var vulnerabilities = if (confirmationTimeout.isPositive()) {
            engine.confirmVulnerabilities(
                entryPoints.toHashSet(),
                engine.getVulnerabilities(),
                confirmationTimeout,
                cancellationTimeout = 30.seconds,
            )
        } else {
            logger.warn { "No time remaining for vulnerability confirmation" }
            engine.getVulnerabilities()
        }
        logger.info { "Total vulnerabilities: ${vulnerabilities.size}" }
        if (options.debugOptions?.enableVulnSummary == true) logger.info { vulnerabilitySummary(vulnerabilities) }

        options.analysisCwe?.let { selectedCwe ->
            vulnerabilities = vulnerabilities.filter {
                val cwe = (it.rule.meta as TaintSinkMeta).cwe
                cwe?.intersect(selectedCwe)?.isNotEmpty() ?: true
            }
            logger.info { "Vulnerabilities with cwe $selectedCwe: ${vulnerabilities.size}" }
        }

        val traceTimeout = (options.ifdsTimeout - analysisStart.elapsedNow()) * 0.90
        if (!traceTimeout.isPositive()) {
            logger.warn { "No time remaining for trace resolution" }
            return emptyList<VulnerabilityWithTrace>() to TaintAnalyzer.Status(
                analysisStatus,
                TaintAnalysisUnitRunnerManager.Status.TIMEOUT,
            )
        }
        val withTraces = generateTraces(entryPoints, vulnerabilities, traceTimeout)
        val resolved = withTraces.filter { it.trace !is TracePathGenerationResult.Failure }
        if (resolved.size != withTraces.size) {
            logger.info { "Filter out ${withTraces.size - resolved.size} vulnerabilities without traces" }
        }
        return resolved to TaintAnalyzer.Status(analysisStatus, engine.status.get())
    }

    private companion object : KLogging()
}
