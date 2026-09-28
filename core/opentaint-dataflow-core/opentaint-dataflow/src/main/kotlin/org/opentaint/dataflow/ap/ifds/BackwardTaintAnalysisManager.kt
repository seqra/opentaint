package org.opentaint.dataflow.ap.ifds

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst

interface BackwardTaintAnalysisManager : TaintAnalysisManager {
    fun createBackwardAnalysisManager(): BackwardTaintAnalysisManager

    fun prepareBackwardRun(analysisEndMethods: Set<CommonMethod>, restrictedTo: Set<BackwardSinkOccurrence>?): Unit =
        error("Not a backward analysis manager")

    fun backwardRunResult(): BackwardRunResult = error("Not a backward analysis manager")
}

data class BackwardSinkOccurrence(val rule: CommonTaintConfigurationSink, val statement: CommonInst)

class BackwardRunResult(
    val seeded: Map<BackwardSinkOccurrence, Set<TaintMarkAccessor>>,
    val vulnerable: Map<BackwardSinkOccurrence, MethodEntryPoint>,
    val exact: Boolean,
)
