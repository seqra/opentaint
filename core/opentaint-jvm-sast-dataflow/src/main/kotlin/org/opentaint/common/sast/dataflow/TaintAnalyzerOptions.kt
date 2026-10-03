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
    val shallowScanApMode: ApMode = ApMode.BaseOnlyField,
    val shallowScanMethodLimit: Int = 5_000,
    val shallowScanTimeLimit: Duration = 30.seconds,
    val shallowRuleSearchExactTimeLimit: Duration = 10.seconds,
)
