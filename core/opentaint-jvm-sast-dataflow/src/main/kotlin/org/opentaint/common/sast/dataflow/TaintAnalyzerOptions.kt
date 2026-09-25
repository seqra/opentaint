package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.ap.ifds.access.ApMode
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

data class TaintAnalyzerOptions(
    val ifdsTimeout: Duration,
    val ifdsApMode: ApMode,
    val symbolicExecutionEnabled: Boolean = false,
    val analysisCwe: Set<Int>? = null,
    val storeSummaries: Boolean = false,
    val experimentalAAInterProcCallDepth: Int = 0,
    val tracePathLimit: Int? = null,
    val debugOptions: DebugOptions? = null,
    val markSet: MarkSetScanOptions = MarkSetScanOptions(),
)

/**
 * Options of the mark-set shallow scan (spec §10), run between the prescan and the full scan.
 *
 * @property enabled record the mark-set program during the prescan and restrict the full scan's rules.
 * @property relaxed option 4* (spec §6.2).
 * @property relevance prune source actions to the needed marks (spec §6.3).
 * @property flowSensitive option 3* (spec §9).
 * @property timeLimit the phase's time budget; exceeding it fails open (spec §6.6).
 * @property maxSites the recorder's site cap; exceeding it fails open.
 * @property maxEdges the recorder's edge cap; exceeding it fails open.
 * @property debugChecks the E1/E2 prescan coverage checks (spec §7, tests only): the recorder keeps
 *   its tables through the full scan, observes it, and [TaintAnalyzer] reports the violations
 *   after it.
 */
data class MarkSetScanOptions(
    val enabled: Boolean = false,
    val relaxed: Boolean = false,
    val relevance: Boolean = true,
    val flowSensitive: Boolean = false,
    val timeLimit: Duration = 30.seconds,
    val maxSites: Int = 20_000_000,
    val maxEdges: Int = 20_000_000,
    val debugChecks: Boolean = false,
)
