package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst

interface BackwardCapableTaintAnalysisManager {
    fun createBackwardAnalysisManager(): BackwardTaintAnalysisManager
}

interface BackwardTaintAnalysisManager : TaintAnalysisManager {
    fun prepareRun(run: BackwardRun)

    fun runResult(): BackwardRunResult
}

data class BackwardSinkOccurrence(
    val rule: CommonTaintConfigurationSink,
    val statement: CommonInst,
)

sealed interface BackwardRun {
    val analysisEndMethods: Set<CommonMethod>

    data class Discovery(
        override val analysisEndMethods: Set<CommonMethod>,
    ) : BackwardRun

    data class Restricted(
        override val analysisEndMethods: Set<CommonMethod>,
        val occurrences: Set<BackwardSinkOccurrence>,
    ) : BackwardRun
}

class BackwardRunResult(
    val seeded: Map<BackwardSinkOccurrence, Set<TaintMarkAccessor>>,
    val vulnerable: Map<BackwardSinkOccurrence, MethodEntryPoint>,
    val exact: Boolean,
)
