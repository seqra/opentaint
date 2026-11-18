package org.opentaint.dataflow.bidi.driver

import org.opentaint.dataflow.bidi.engine.RunConfig
import org.opentaint.dataflow.bidi.engine.RunMethodAnalyzer
import org.opentaint.dataflow.bidi.engine.RunResult
import org.opentaint.dataflow.bidi.engine.RunStatus
import java.util.Collections
import kotlin.time.Duration

interface IterationPolicy {
    val fieldLimitSchedule: FieldLimitSchedule get() = FieldLimitSchedule.REPEAT_RUN1
    fun fieldLimit(runIndex: Int): Int

    /** Called only after a complete forward run and the empty-demand stop check. */
    fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>): Boolean

    /** Distinguish a policy cutoff from empty-demand convergence. */
    fun stopReason(run: RunConfig): EndReason = EndReason.POLICY

    fun timeout(run: RunConfig, remaining: Duration): Duration = remaining
}

/** The complete forward barrier at this index is the final allowed barrier. */
class HardRunLimitPolicy(
    private val delegate: IterationPolicy,
    val lastForwardRun: Int = 11,
) : IterationPolicy by delegate {
    init {
        require(lastForwardRun >= 1 && lastForwardRun % 2 == 1) {
            "The last allowed run must be a positive forward (odd) run"
        }
    }

    override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>): Boolean =
        run.index < lastForwardRun && delegate.continueAfter(run, result, frontiers)

    override fun stopReason(run: RunConfig): EndReason =
        if (run.index >= lastForwardRun) EndReason.RUN_LIMIT else delegate.stopReason(run)
}

/** RUN_INDEX is an opt-in experiment. The normal schedule stays unchanged. */
enum class FieldLimitSchedule {
    REPEAT_RUN1, RUN_INDEX;

    fun fieldLimit(runIndex: Int): Int {
        require(runIndex >= 1) { "The run index must be positive" }
        return when (this) {
            REPEAT_RUN1 -> maxOf(1, runIndex - 1)
            RUN_INDEX -> runIndex
        }
    }
}

/** Run 1 and the first exact backward run both use field limit 1. */
object IncreasingLimits : IterationPolicy {
    override fun fieldLimit(runIndex: Int): Int = fieldLimitSchedule.fieldLimit(runIndex)

    override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>): Boolean = true
}

object RunIndexLimits : IterationPolicy {
    override val fieldLimitSchedule: FieldLimitSchedule = FieldLimitSchedule.RUN_INDEX
    override fun fieldLimit(runIndex: Int): Int = fieldLimitSchedule.fieldLimit(runIndex)

    override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>): Boolean = true
}

/** The project entry point reads the setting once when it selects the policy. */
fun configuredIncreasingLimits(
    value: String? = System.getProperty("opentaint.bidi.fieldLimitSchedule"),
): IterationPolicy = HardRunLimitPolicy(when (value) {
    null, "REPEAT_RUN1" -> IncreasingLimits
    "RUN_INDEX" -> RunIndexLimits
    else -> error("Invalid opentaint.bidi.fieldLimitSchedule=$value; use REPEAT_RUN1 or RUN_INDEX")
})

class FixedLimits(limits: List<Int>) : IterationPolicy {
    private val limits: List<Int> = Collections.unmodifiableList(ArrayList(limits))

    override fun fieldLimit(runIndex: Int): Int = limits[runIndex - 1]

    override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>): Boolean =
        run.index + 2 <= limits.size
}

sealed interface Next {
    class Run(val config: RunConfig) : Next
    class End(val status: RunStatus, val reason: EndReason = EndReason.ABNORMAL) : Next
}
