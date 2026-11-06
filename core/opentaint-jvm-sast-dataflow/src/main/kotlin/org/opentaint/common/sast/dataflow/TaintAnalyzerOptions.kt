package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.jvm.ap.ifds.AliasAnalysisMode
import kotlin.time.Duration

data class TaintAnalyzerOptions(
    val ifdsTimeout: Duration,
    val ifdsApMode: ApMode,
    val symbolicExecutionEnabled: Boolean = false,
    val analysisCwe: Set<Int>? = null,
    val storeSummaries: Boolean = false,
    val experimentalAAInterProcCallDepth: Int = 0,
    val experimentalAliasAnalysisMode: AliasAnalysisMode = AliasAnalysisMode.DSU,
    val tracePathLimit: Int? = null,
    val debugOptions: DebugOptions? = null,
)
