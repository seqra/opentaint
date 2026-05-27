package org.opentaint.jvm.sast.project

import kotlin.time.Duration
import org.opentaint.jvm.sast.dataflow.DataFlowApproximationLoader
import org.opentaint.jvm.sast.dataflow.TaintAnalyzerOptions

data class ProjectAnalysisOptions(
    val common: CommonAnalysisOptions = CommonAnalysisOptions(),
    val cwe: List<Int> = emptyList(),
    val useSymbolicExecution: Boolean = false,
    val symbolicExecutionTimeout: Duration = Duration.ZERO,
    val projectKind: ProjectKind = ProjectKind.UNKNOWN,
    val storeSummaries: Boolean = false,
    val experimentalAAInterProcCallDepth: Int = 1,
    val approximationOptions: DataFlowApproximationLoader.Options = DataFlowApproximationLoader.Options(),
) {
    val summariesApMode get() = common.ifdsApMode.takeIf { storeSummaries }

    fun taintAnalyzerOptions() = TaintAnalyzerOptions(
        ifdsTimeout = common.ifdsAnalysisTimeout,
        ifdsApMode = common.ifdsApMode,
        symbolicExecutionEnabled = useSymbolicExecution,
        analysisCwe = cwe.takeIf { it.isNotEmpty() }?.toSet(),
        storeSummaries = storeSummaries,
        experimentalAAInterProcCallDepth = experimentalAAInterProcCallDepth,
        debugOptions = common.debugOptions,
    )
}
