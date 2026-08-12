package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver.MethodCallResolutionResult
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.graph.PIRUnknownFunction
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction

class PIRMethodCallResolver(
    private val callResolver: PIRCallResolver,
    private val runner: TaintAnalysisUnitRunner,
) : MethodCallResolver {

    /**
     * Synthetic [org.opentaint.dataflow.python.graph.PIRUnknownFunction]s are only used by the call flow
     * function for rule lookup — they have no CFG to step into, so they
     * must not be surfaced as resolved interprocedural targets.
     */
    private fun Set<PIRFunction>.realCallees(): List<PIRFunction> =
        filter { it !is PIRUnknownFunction }

    override fun resolveMethodCall(
        callerContext: MethodAnalysisContext,
        callExpr: CommonCallExpr,
        location: CommonInst,
        handler: MethodAnalyzer.MethodCallHandler,
        failureHandler: MethodAnalyzer.MethodCallResolutionFailureHandler,
    ) {
        val pirCall = location as PIRCall
        val callees = callResolver.resolveCall(pirCall).realCallees()
        val analyzer = runner.getMethodAnalyzer(callerContext.methodEntryPoint)
        if (callees.isEmpty()) {
            analyzer.handleMethodCallResolutionFailure(callExpr, failureHandler)
            return
        }
        for (callee in callees) {
            analyzer.handleResolvedMethodCall(MethodWithContext(callee, EmptyMethodContext), handler)
        }
    }

    override fun resolvedMethodCalls(
        callerContext: MethodAnalysisContext,
        callExpr: CommonCallExpr,
        location: CommonInst,
    ): List<MethodCallResolutionResult> {
        val pirCall = location as PIRCall
        val callees = callResolver.resolveCall(pirCall).realCallees()
        if (callees.isEmpty()) return listOf(MethodCallResolutionResult.ResolutionFailure)
        return callees.map {
            MethodCallResolutionResult.ResolvedMethod(MethodWithContext(it, EmptyMethodContext))
        }
    }
}
