package org.opentaint.common.sast.dataflow

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.markset.MarkSetInput
import org.opentaint.dataflow.ap.ifds.markset.MarkSetOptions
import org.opentaint.dataflow.ap.ifds.markset.MarkSetRecorder
import org.opentaint.dataflow.ap.ifds.markset.MarkSetResult
import org.opentaint.dataflow.ap.ifds.markset.MarkSetScan
import org.opentaint.dataflow.ap.ifds.markset.MarkSetStats
import org.opentaint.dataflow.ap.ifds.markset.SiteKind
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.time.Duration
import kotlin.time.TimeSource

/** The mark-set phase's result (spec §10): a selection to install, or fail-open (spec §6.6). */
sealed interface MarkSetOutcome {
    /** The phase's one INFO log line (spec §10, Logging). */
    fun logLine(): String

    /**
     * @property rules the selection for [org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.selectStatementRules].
     * @property covered the statements the prescan queried rules at (the provider's fallback, spec §10).
     * @property roots the number of roots in the sealed program.
     * @property selectedActions the number of source actions in [rules].
     * @property baselineActions the number of source actions over every recorded source site.
     * @property elapsed the phase's time, sealing included.
     */
    data class Selected(
        val rules: ActionableRules,
        val covered: Set<CommonInst>,
        val stats: MarkSetStats,
        val roots: Int = 0,
        val selectedActions: Int = 0,
        val baselineActions: Int = 0,
        val elapsed: Duration = Duration.ZERO,
    ) : MarkSetOutcome {
        override fun logLine(): String =
            "markset: time=${elapsed.inWholeMilliseconds}ms methods=${stats.methods} edges=${stats.edges} " +
                "sites=${stats.sites} signatures=${stats.signatures} roots=$roots " +
                "rootSets=${stats.distinctRootSets} applicableSinks=${stats.applicableSinks} " +
                "neededMarks=${stats.neededMarks} selectedActions=$selectedActions/baselineActions=$baselineActions"
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

/**
 * Runs the mark-set phase between the prescan and the full scan (spec §10): seals [recorder],
 * runs [MarkSetScan] and converts its result to [ActionableRules]. It runs no IFDS.
 *
 * Fails open (spec §6.6), in this order, when the prescan did not complete with status OK,
 * when summaries are stored, when the recorder hit a cap, when the phase exceeds
 * [MarkSetScanOptions.timeLimit], or when it runs out of memory. [onSealed] observes the sealed
 * input (a test hook).
 */
fun runMarkSetPhase(
    recorder: MarkSetRecorder,
    roots: Collection<CommonMethod>,
    prescanOk: Boolean,
    storeSummaries: Boolean,
    options: MarkSetScanOptions,
    onSealed: (MarkSetInput) -> Unit = {},
): MarkSetOutcome {
    // Stop recording first: a prescan that timed out may still have runners winding down.
    recorder.active = false

    if (!prescanOk) return MarkSetOutcome.FailOpen("prescan incomplete")
    if (storeSummaries) return MarkSetOutcome.FailOpen("stored summaries")
    if (recorder.overflow) return MarkSetOutcome.FailOpen("recorder cap")

    val start = TimeSource.Monotonic.markNow()
    val checkCancelled = {
        if (start.elapsedNow() > options.timeLimit) throw MarkSetTimeLimitExceeded()
    }

    return try {
        val input = recorder.seal(roots)
        onSealed(input)
        checkCancelled()

        val scanOptions = MarkSetOptions(relaxed = options.relaxed, relevance = options.relevance)
        val result = MarkSetScan.run(input.program, scanOptions, checkCancelled)
        checkCancelled()

        input.toSelection(result, options, start.elapsedNow())
    } catch (e: MarkSetTimeLimitExceeded) {
        MarkSetOutcome.FailOpen("time limit")
    } catch (e: OutOfMemoryError) {
        MarkSetOutcome.FailOpen("memory")
    } catch (e: Exception) {
        logger.error(e) { "Mark-set phase failed" }
        MarkSetOutcome.FailOpen("error: $e")
    }
}

/**
 * Converts the scan's result to [ActionableRules] (spec §6.4, §10). An applicable sink maps to
 * the empty action set. An applicable source maps to its `AssignMark`s whose mark is needed (all
 * of them without relevance), merged by union over its sites, and is dropped when none remain.
 * Pass-through sites are never emitted: pass-throughs are never restricted.
 */
private fun MarkSetInput.toSelection(
    result: MarkSetResult,
    options: MarkSetScanOptions,
    elapsed: Duration,
): MarkSetOutcome.Selected {
    val markIds = HashMap<String, Int>(markNames.size)
    markNames.forEachIndexed { id, name -> markIds[name] = id }

    fun isNeeded(markName: String): Boolean {
        if (!options.relevance) return true
        val id = markIds[markName] ?: return false
        return result.needed[id]
    }

    val rules = HashMap<CommonInst, HashMap<CommonTaintConfigurationItem, MutableSet<CommonTaintAction>>>()
    var baselineActions = 0

    for ((i, site) in program.sites.withIndex()) {
        if (site.kind != SiteKind.SOURCE) continue
        baselineActions += (sites[i].rule as? TaintConfigurationSource)?.actionsAfter?.size ?: 0
    }

    var i = result.applicable.nextSetBit(0)
    while (i >= 0) {
        val ref = sites[i]
        when (program.sites[i].kind) {
            SiteKind.SINK -> rules.getOrPut(ref.statement, ::HashMap).getOrPut(ref.rule, ::hashSetOf)

            SiteKind.SOURCE -> {
                val rule = ref.rule as TaintConfigurationSource
                val actions = rule.actionsAfter.filter { isNeeded(it.mark.name) }
                if (actions.isNotEmpty()) {
                    rules.getOrPut(ref.statement, ::HashMap).getOrPut(ref.rule, ::hashSetOf).addAll(actions)
                }
            }

            SiteKind.PASS_THROUGH -> {}
        }
        i = result.applicable.nextSetBit(i + 1)
    }

    val selectedActions = rules.values.sumOf { stmtRules ->
        stmtRules.entries.sumOf { (rule, actions) -> if (rule is TaintConfigurationSource) actions.size else 0 }
    }

    return MarkSetOutcome.Selected(
        rules = rules,
        covered = coveredStatements,
        stats = result.stats,
        roots = program.roots.size,
        selectedActions = selectedActions,
        baselineActions = baselineActions,
        elapsed = elapsed,
    )
}
