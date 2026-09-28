package org.opentaint.dataflow.ap.ifds

import org.opentaint.ir.api.common.CommonMethod

interface BackwardTaintAnalysisManager : TaintAnalysisManager {
    fun createBackwardAnalysisManager(analysisEndMethods: Set<CommonMethod>): TaintAnalysisManager
}
