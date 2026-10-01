package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.ap.ifds.access.ApMode
import kotlin.time.Duration

enum class AnalysisDirection {
    FORWARD, BACKWARD;

    companion object {
        const val PROPERTY = "opentaint.analysis.direction"
        const val ENV_VARIABLE = "OPENTAINT_ANALYSIS_DIRECTION"

        fun fromEnvironment(): AnalysisDirection {
            val value = System.getProperty(PROPERTY)?.takeIf { it.isNotBlank() }
                ?: System.getenv(ENV_VARIABLE)?.takeIf { it.isNotBlank() }
                ?: return FORWARD
            return entries.firstOrNull { it.name.equals(value.trim(), ignoreCase = true) }
                ?: error("Unknown analysis direction: $value")
        }
    }
}

data class TaintAnalyzerOptions(
    val ifdsTimeout: Duration,
    val ifdsApMode: ApMode,
    val symbolicExecutionEnabled: Boolean = false,
    val analysisCwe: Set<Int>? = null,
    val storeSummaries: Boolean = false,
    val experimentalAAInterProcCallDepth: Int = 0,
    val tracePathLimit: Int? = null,
    val debugOptions: DebugOptions? = null,
    val analysisDirection: AnalysisDirection = AnalysisDirection.fromEnvironment(),
)
