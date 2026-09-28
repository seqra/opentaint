package org.opentaint.dataflow.ap.ifds

interface BackwardTaintAnalysisManager : TaintAnalysisManager {
    fun createBackwardAnalysisManager(): TaintAnalysisManager
}
