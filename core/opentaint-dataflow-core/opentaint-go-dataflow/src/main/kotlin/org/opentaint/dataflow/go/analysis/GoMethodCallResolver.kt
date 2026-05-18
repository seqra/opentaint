package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver.MethodCallResolutionResult
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoCallResolver
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.inst.GoIRInst

/**
 * Framework adapter wrapping GoCallResolver to implement MethodCallResolver.
 */
class GoMethodCallResolver(
    private val callResolver: GoCallResolver,
    private val runner: TaintAnalysisUnitRunner,
) : MethodCallResolver {

    override fun resolveMethodCall(
        callerContext: MethodAnalysisContext,
        callExpr: CommonCallExpr,
        location: CommonInst,
        handler: MethodAnalyzer.MethodCallHandler,
        failureHandler: MethodAnalyzer.MethodCallResolutionFailureHandler,
    ) {
        val goCallExpr = callExpr as GoCallExpr
        val resolved = callResolver.resolve(goCallExpr.callInfo, location as GoIRInst)
        val analyzer = runner.getMethodAnalyzer(callerContext.methodEntryPoint)

        if (resolved.isNullOrEmpty()) {
            analyzer.handleMethodCallResolutionFailure(callExpr, failureHandler)
        } else {
            for (callee in resolved) {
                analyzer.handleResolvedMethodCall(MethodWithContext(callee, EmptyMethodContext), handler)
            }
        }
    }

    override fun resolvedMethodCalls(
        callerContext: MethodAnalysisContext,
        callExpr: CommonCallExpr,
        location: CommonInst,
    ): List<MethodCallResolutionResult> {
        val goCallExpr = callExpr as GoCallExpr
        val resolved = callResolver.resolve(goCallExpr.callInfo, location as GoIRInst)
            ?: return listOf(MethodCallResolutionResult.ResolutionFailure)

        return resolved.map {
            MethodCallResolutionResult.ResolvedMethod(MethodWithContext(it, EmptyMethodContext))
        }
    }
}
