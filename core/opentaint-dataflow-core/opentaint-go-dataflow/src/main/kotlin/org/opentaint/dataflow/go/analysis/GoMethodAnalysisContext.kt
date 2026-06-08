package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.go.GoClosureTracker.ClosureTracker
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.dataflow.go.rules.GoTaintAnalysisContext
import org.opentaint.dataflow.util.int2ObjectMap
import org.opentaint.ir.go.api.GoIRFunction

/**
 * Per-method analysis context for Go. Significantly simpler than JVM's.
 */
class GoMethodAnalysisContext(
    override val methodEntryPoint: MethodEntryPoint,
    val taint: GoTaintAnalysisContext,
    val aliasAnalysis: GoLocalAliasAnalysis,
) : MethodAnalysisContext {
    override val methodCallFactMapper: MethodCallFactMapper
        get() = GoMethodCallFactMapper

    val method: GoIRFunction
        get() = methodEntryPoint.method as GoIRFunction

    val closureCallResolution = int2ObjectMap<ClosureTracker>()
}
