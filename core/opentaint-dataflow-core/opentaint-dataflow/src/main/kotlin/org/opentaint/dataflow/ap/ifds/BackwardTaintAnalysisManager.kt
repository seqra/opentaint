package org.opentaint.dataflow.ap.ifds

import org.opentaint.ir.api.common.CommonMethod
import kotlin.time.Duration

interface BackwardTaintAnalysisManager : TaintAnalysisManager {
    fun createBackwardAnalysisManager(): BackwardTaintAnalysisManager

    fun prepareNextBackwardRun(analysisEndMethods: Set<CommonMethod>, timeLeft: Duration): Duration? =
        error("Not a backward analysis manager")
}
