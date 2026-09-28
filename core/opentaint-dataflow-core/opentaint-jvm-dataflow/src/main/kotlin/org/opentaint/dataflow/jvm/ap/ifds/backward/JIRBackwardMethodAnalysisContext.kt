package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext

class JIRBackwardMethodAnalysisContext(
    forward: JIRMethodAnalysisContext,
    methodEntryPoint: MethodEntryPoint,
) : JIRMethodAnalysisContext(
    forward.analysisManager,
    forward.refManager,
    methodEntryPoint,
    forward.factTypeChecker,
    forward.localVariableReachability,
    forward.aliasAnalysis,
    JIRBackwardTaintAnalysisContext(
        forward.taint.taintSinkTracker,
        forward.analysisManager.taintConfig,
        forward.taint.externalMethodTracker,
        forward.taint.relevantRuleIds,
    ),
) {
    val backwardTaint get() = taint as JIRBackwardTaintAnalysisContext

    override val methodCallFactMapper: MethodCallFactMapper
        get() = JIRBackwardMethodCallFactMapper
}
