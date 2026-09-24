package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase

interface JIRAnalysisManagerBase {
    val phase: Phase
    val params: JIRAnalysisManager.Params
}
