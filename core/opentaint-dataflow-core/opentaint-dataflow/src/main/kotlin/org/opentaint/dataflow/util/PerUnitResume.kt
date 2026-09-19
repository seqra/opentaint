package org.opentaint.dataflow.util

/**
 * Let a unit release its own delayed edges when its own work list drains.
 *
 * The shipped resume is a GLOBAL barrier: `TaintAnalysisUnitRunnerManager.handleEventProcessed`
 * releases delayed edges only when the total event count across every unit reaches exactly zero.
 * Near the end of each wave only a few units still have work, so the rest sit idle -- measured, 21%
 * of workers RUNNABLE and 62% of `Progress` samples exactly zero.
 *
 * Releasing a unit's own delayed analyzers when that unit has nothing else to do cannot lose a
 * finding: the delay is a SCHEDULE, `updateFactDepthLimit` replays every delayed edge, and doing it
 * sooner only makes work available sooner. Completion still requires global quiescence with no
 * delayed analyzer anywhere.
 */
object PerUnitResume {
    val enabled: Boolean =
        System.getProperty("opentaint.perUnitResume")?.toBooleanStrictOrNull() ?: false

    /**
     * How many times a unit may resume ITSELF before it must wait for the global barrier again.
     * 0 means no limit, which is the plain per-unit resume.
     *
     * MEASURED, and this is why the window exists. The unlimited form removes the starvation
     * completely -- queue 10 -> 36,975, events 1,345,135 -> 3,276,803 -- and it LOSES
     * `ssrf@HttpTask:173`, because each unit's depth ladder races ahead: `analyzedAdd` grows 4.9x
     * and the run goes DEEP before it goes WIDE. The global barrier is breadth-first order across
     * units, and the findings depend on that order.
     *
     * A window keeps a unit from getting more than `W` rungs ahead of the wave it belongs to, so it
     * buys throughput without abandoning the order. `W = 1` is close to the barrier; unlimited is
     * the arm that loses the finding.
     */
    val window: Int =
        System.getProperty("opentaint.perUnitResumeWindow")?.toIntOrNull() ?: 0
}
