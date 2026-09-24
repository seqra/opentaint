package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManagerBase
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.util.SoftReferenceManager
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRBackwardMethodAnalysisContext(
    analysisManager: JIRAnalysisManagerBase,
    refManager: SoftReferenceManager,
    methodEntryPoint: MethodEntryPoint,
    factTypeChecker: JIRFactTypeChecker,
    localVariableReachability: JIRLocalVariableReachability,
    aliasAnalysis: JIRLocalAliasAnalysis?,
    taint: JIRTaintAnalysisContext,
    val forwardEntryPoint: JIRInst?,
    val findings: JIRBackwardFindingTracker,
) : JIRMethodAnalysisContext(
    analysisManager,
    refManager,
    methodEntryPoint,
    factTypeChecker,
    localVariableReachability,
    aliasAnalysis,
    taint,
) {
    override val methodCallFactMapper: MethodCallFactMapper
        get() = JIRBackwardMethodCallFactMapper
}
