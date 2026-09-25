package org.opentaint.common.sast.dataflow

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.markset.FlowSensitiveScan
import org.opentaint.dataflow.ap.ifds.markset.MarkSetInput
import org.opentaint.dataflow.ap.ifds.markset.MarkSetOptions
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
import org.opentaint.dataflow.ap.ifds.markset.MarkSetResult
import org.opentaint.dataflow.ap.ifds.markset.MarkSetScan
import org.opentaint.dataflow.ap.ifds.markset.MarkSetStats
import org.opentaint.dataflow.ap.ifds.markset.MethodCfgSource
import org.opentaint.dataflow.ap.ifds.markset.MethodCfgUnavailable
import org.opentaint.dataflow.ap.ifds.markset.SiteKind
import org.opentaint.dataflow.ap.ifds.markset.SiteRef
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.time.Duration
import kotlin.time.TimeSource

/** The mark-set phase's result (spec §10): a selection to install, or fail-open (spec §6.6). */
sealed interface MarkSetOutcome {
    /** The phase's one INFO log line (spec §10, Logging). */
    fun logLine(): String

    /**
     * The action, sink and source-rule counts are over unique `(statement, rule)` pairs.
     * Static-field sources are never restricted (spec §6.4), so they are in none of them.
     *
     * @property rules the selection for [org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.selectStatementRules].
     * @property covered the statements the prescan queried rules at (the provider's fallback, spec §10).
     * @property roots the number of roots in the sealed program.
     * @property selectedActions the number of source actions in [rules].
     * @property baselineActions the number of distinct source actions over every recorded
     *   `(statement, source rule)` pair.
     * @property selectedSinks the `(statement, sink rule)` pairs in [rules].
     * @property baselineSinks the recorded `(statement, sink rule)` pairs.
     * @property selectedSourceRules the `(statement, source rule)` pairs in [rules] (with >= 1 action).
     * @property baselineSourceRules the recorded `(statement, source rule)` pairs.
     * @property elapsed the phase's time, sealing included.
     * @property sealTime the part of [elapsed] spent sealing the recorder.
     * @property scanTime the part of [elapsed] spent in the scan.
     * @property neededMarks the names of the needed marks (spec §6.3), or `null` without relevance
     *   (every mark is needed then). The E10 debug diff compares the facts of these marks.
     * @property recorderBytes the recorder's estimated size when the phase started
     *   ([MarkSetRecorder.estimatedBytes]; its cap is [MarkSetScanOptions.maxRecorderBytes]).
     */
    data class Selected(
        val rules: ActionableRules,
        val covered: Set<CommonInst>,
        val stats: MarkSetStats,
        val roots: Int = 0,
        val selectedActions: Int = 0,
        val baselineActions: Int = 0,
        val selectedSinks: Int = 0,
        val baselineSinks: Int = 0,
        val selectedSourceRules: Int = 0,
        val baselineSourceRules: Int = 0,
        val elapsed: Duration = Duration.ZERO,
        val sealTime: Duration = Duration.ZERO,
        val scanTime: Duration = Duration.ZERO,
        val neededMarks: Set<String>? = null,
        val recorderBytes: Long = 0,
    ) : MarkSetOutcome {
        override fun logLine(): String =
            "markset: time=${elapsed.inWholeMilliseconds}ms seal=${sealTime.inWholeMilliseconds}ms " +
                "scan=${scanTime.inWholeMilliseconds}ms methods=${stats.methods} edges=${stats.edges} " +
                "sites=${stats.sites} signatures=${stats.signatures} roots=$roots " +
                "rootSets=${stats.distinctRootSets} applicableSinks=${stats.applicableSinks} " +
                "neededMarks=${stats.neededMarks} selectedActions=$selectedActions/baselineActions=$baselineActions " +
                "selectedSinks=$selectedSinks/baselineSinks=$baselineSinks " +
                "sourceRules=$selectedSourceRules/$baselineSourceRules " +
                "recorderMb=${recorderBytes / (1024 * 1024)}" +
                if (stats.rootPoints > 0) " rootPoints=${stats.rootPoints}" else ""
    }

    /** The full scan runs with the baseline rules. */
    data class FailOpen(val reason: String) : MarkSetOutcome {
        override fun logLine(): String = "markset: fail-open ($reason)"
    }
}

private class MarkSetTimeLimitExceeded : RuntimeException("mark-set time limit") {
    override fun fillInStackTrace(): Throwable = this
}

private val logger = object : KLogging() {}.logger

private const val FLOW_SENSITIVE_CFG = "flow-sensitive cfg"
private const val FLOW_SENSITIVE_SIZE = "flow-sensitive size"

/**
 * Runs the mark-set phase between the prescan and the full scan (spec §10): seals [recorder],
 * runs [MarkSetScan] (or [FlowSensitiveScan] under [MarkSetScanOptions.flowSensitive], spec §9)
 * and converts its result to [ActionableRules]. It runs no IFDS.
 *
 * Fails open (spec §6.6), in this order, when the prescan did not complete with status OK,
 * when summaries are stored, when the recorder hit a cap, when the phase exceeds
 * [MarkSetScanOptions.timeLimit], or when it runs out of memory. Under option 3* it also fails
 * open when the statement graph is unavailable (no [cfgSource], a recorder without call points,
 * or a statement outside its method's graph: "flow-sensitive cfg") and when the scan would visit
 * more than [maxRootPoints] `(root, statement)` pairs ("flow-sensitive size"). [onSealed] observes
 * the sealed input (a test hook).
 *
 * The recorder is released on every path, except that under [MarkSetScanOptions.debugChecks] (with
 * a recorder made with [MarkSetRecorder.debugChecks]) a selection keeps it and starts observing the
 * full scan (spec §7, E1/E2): the caller then calls [MarkSetRecorder.checkCoverage] after the full
 * scan, and releases it.
 *
 * @param cfgSource the engine's statement graphs, required by option 3* only.
 */
fun runMarkSetPhase(
    recorder: MarkSetRecorder,
    roots: Collection<CommonMethod>,
    prescanOk: Boolean,
    storeSummaries: Boolean,
    options: MarkSetScanOptions,
    onSealed: (MarkSetInput) -> Unit = {},
    cfgSource: MethodCfgSource? = null,
    maxRootPoints: Long = FlowSensitiveScan.MAX_ROOT_POINTS,
): MarkSetOutcome {
    // Stop recording first: a prescan that timed out may still have runners winding down.
    recorder.active = false

    val failOpen = when {
        !prescanOk -> "prescan incomplete"
        storeSummaries -> "stored summaries"
        recorder.overflow -> "recorder cap"
        options.flowSensitive && (cfgSource == null || !recorder.recordCalls) -> FLOW_SENSITIVE_CFG
        else -> null
    }
    if (failOpen != null) {
        recorder.release()
        return MarkSetOutcome.FailOpen(failOpen)
    }

    val start = TimeSource.Monotonic.markNow()
    val checkCancelled = {
        if (start.elapsedNow() > options.timeLimit) throw MarkSetTimeLimitExceeded()
    }

    val debugChecks = options.debugChecks && recorder.debugChecks
    val recorderBytes = recorder.estimatedBytes
    var outcome: MarkSetOutcome? = null
    return try {
        val input = recorder.seal(roots, cfgSource.takeIf { options.flowSensitive })
        // Only the selection and the covered statements survive into the full scan, but the debug
        // checks need the prescan's tables.
        if (!debugChecks) recorder.release()
        val sealTime = start.elapsedNow()
        onSealed(input)
        checkCancelled()

        val scanOptions = MarkSetOptions(relaxed = options.relaxed, relevance = options.relevance)
        val result = if (options.flowSensitive) {
            if (FlowSensitiveScan.rootPoints(input.program, maxRootPoints) > maxRootPoints) {
                return MarkSetOutcome.FailOpen(FLOW_SENSITIVE_SIZE)
            }
            FlowSensitiveScan.run(input.program, scanOptions, checkCancelled)
        } else {
            MarkSetScan.run(input.program, scanOptions, checkCancelled)
        }
        val scanTime = start.elapsedNow() - sealTime
        checkCancelled()

        input.toSelection(result, options).copy(
            elapsed = start.elapsedNow(), sealTime = sealTime, scanTime = scanTime, recorderBytes = recorderBytes,
        ).also { outcome = it }
    } catch (e: MarkSetTimeLimitExceeded) {
        MarkSetOutcome.FailOpen("time limit")
    } catch (e: MethodCfgUnavailable) {
        logger.warn { "Mark-set phase: ${e.message}" }
        MarkSetOutcome.FailOpen(FLOW_SENSITIVE_CFG)
    } catch (e: OutOfMemoryError) {
        MarkSetOutcome.FailOpen("memory")
    } catch (e: Exception) {
        logger.error(e) { "Mark-set phase failed" }
        MarkSetOutcome.FailOpen("error: $e")
    } finally {
        if (debugChecks && outcome is MarkSetOutcome.Selected) {
            recorder.startObserving()
        } else {
            recorder.release()
        }
    }
}

/**
 * Converts the scan's result to [ActionableRules] (spec §6.4, §10). An applicable sink maps to
 * the empty action set. An applicable source maps to its `AssignMark`s whose mark is needed (all
 * of them without relevance), merged by union over its sites, and is dropped when none remain.
 * Pass-through sites and static-field sources are never emitted: the provider never restricts
 * them. The counts are over unique `(statement, rule)` pairs of the restrictable kinds only.
 */
private fun MarkSetInput.toSelection(
    result: MarkSetResult,
    options: MarkSetScanOptions,
): MarkSetOutcome.Selected {
    val markIds = HashMap<String, Int>(markNames.size)
    markNames.forEachIndexed { id, name -> markIds[name] = id }

    fun isNeeded(markName: String): Boolean {
        if (!options.relevance) return true
        val id = markIds[markName] ?: return false
        return result.needed[id]
    }

    // Baseline: every recorded restrictable (statement, rule) pair. The sites of one pair are
    // contiguous in the sealed input, so a pair is counted where it starts.
    var baselineSourceRules = 0
    var baselineActions = 0
    var baselineSinks = 0
    for ((i, site) in program.sites.withIndex()) {
        val ref = sites[i]
        if (i > 0 && sites[i - 1].let { it.statement === ref.statement && it.rule === ref.rule }) continue
        when (site.kind) {
            SiteKind.SOURCE -> ref.restrictableSource()?.let {
                baselineSourceRules++
                baselineActions += it.actionsAfter.distinct().size
            }
            SiteKind.SINK -> baselineSinks++
            SiteKind.PASS_THROUGH -> {}
        }
    }

    val rules = HashMap<CommonInst, HashMap<CommonTaintConfigurationItem, MutableSet<CommonTaintAction>>>()

    var i = result.applicable.nextSetBit(0)
    while (i >= 0) {
        val ref = sites[i]
        when (program.sites[i].kind) {
            SiteKind.SINK -> rules.getOrPut(ref.statement, ::HashMap).getOrPut(ref.rule, ::hashSetOf)

            SiteKind.SOURCE -> {
                val rule = ref.restrictableSource()
                val actions = rule?.actionsAfter?.filter { isNeeded(it.mark.name) }.orEmpty()
                if (actions.isNotEmpty()) {
                    rules.getOrPut(ref.statement, ::HashMap).getOrPut(ref.rule, ::hashSetOf).addAll(actions)
                }
            }

            SiteKind.PASS_THROUGH -> {}
        }
        i = result.applicable.nextSetBit(i + 1)
    }

    var selectedSourceRules = 0
    var selectedActions = 0
    var selectedSinks = 0
    for (stmtRules in rules.values) {
        for ((rule, actions) in stmtRules) {
            if (rule is TaintConfigurationSource) {
                selectedSourceRules++
                selectedActions += actions.size
            } else {
                selectedSinks++
            }
        }
    }

    return MarkSetOutcome.Selected(
        rules = rules,
        covered = coveredStatements,
        stats = result.stats,
        roots = program.roots.size,
        selectedActions = selectedActions,
        baselineActions = baselineActions,
        selectedSinks = selectedSinks,
        baselineSinks = baselineSinks,
        selectedSourceRules = selectedSourceRules,
        baselineSourceRules = baselineSourceRules,
        neededMarks = if (options.relevance) markNames.filterTo(hashSetOf(), ::isNeeded) else null,
    )
}

/** The site's source rule if the provider restricts it (every source kind but static-field). */
private fun SiteRef.restrictableSource(): TaintConfigurationSource? =
    (rule as? TaintConfigurationSource)?.takeIf { it !is TaintStaticFieldSource }
