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
    val rules get() = (analysisManager as JIRBackwardAnalysisManager).rules

    override val methodCallFactMapper: MethodCallFactMapper
        get() = JIRBackwardMethodCallFactMapper
}
