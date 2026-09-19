package org.opentaint.dataflow.util

/**
 * Roll back the global event count when a work-list `trySend` is dropped.
 *
 * `TaintAnalysisUnitRunner.addUnprocessedAnyEvent` counts an event globally BEFORE it posts it, and
 * ignores the result of `trySend`. Once the channel is cancelled or replaced the post fails, the
 * event is never processed, and the count keeps it forever. `handleEventProcessed` resumes delayed
 * units only when that count reaches EXACTLY zero, so one lost event strands every delayed edge in
 * the analysis.
 *
 * Default ON: leaving a poisoned counter is never correct. The flag exists so the repair can be
 * measured against its own control from one jar (GUIDELINES 4.7), and `ExplosionStats.eventDropped`
 * says whether it ever fires at all (GUIDELINES 4.6).
 */
object EventLeakRepair {
    val enabled: Boolean =
        System.getProperty("opentaint.repairEventLeak")?.toBooleanStrictOrNull() ?: true
}
