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
    forward.taint,
) {
    val forwardEntryPoint = forward.methodEntryPoint.statement

    val findings get() = (analysisManager as JIRBackwardAnalysisManager).findings

    val starUnroller get() = (analysisManager as JIRBackwardAnalysisManager).starUnroller

    override val methodCallFactMapper: MethodCallFactMapper
        get() = JIRBackwardMethodCallFactMapper
}
