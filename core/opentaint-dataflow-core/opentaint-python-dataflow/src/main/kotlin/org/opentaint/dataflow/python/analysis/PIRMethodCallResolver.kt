package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer.MethodCallHandler
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver.MethodCallResolutionResult
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.impl.python.PIRUnknownFunction

class PIRMethodCallResolver(
    private val callResolver: PIRCallResolver,
    private val runner: TaintAnalysisUnitRunner,
) : MethodCallResolver {

    /**
     * Synthetic [PIRUnknownFunction]s are only used by the call flow
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
        val callees = callResolver.resolve(pirCall).realCallees()
        val analyzer = runner.getMethodAnalyzer(callerContext.methodEntryPoint)
        if (callees.isEmpty()) {
            analyzer.handleMethodCallResolutionFailure(callExpr, failureHandler)
            return
        }
        val factMapper = callerContext.methodCallFactMapper as PIRMethodCallFactMapper
        for (callee in callees) {
            // Apply the implicit-parameter offset to the callee-frame entry
            // base. The flow function produced an offset-free Argument(i)
            // based on call.args; offsetEnter shifts it to Argument(i + offset)
            // for the callee's frame. Out-of-range Arguments are dropped.
            val rebasedHandler = rebaseStartFactBase(handler, pirCall, callee, factMapper) ?: continue
            analyzer.handleResolvedMethodCall(MethodWithContext(callee, EmptyMethodContext), rebasedHandler)
        }
    }

    private fun rebaseStartFactBase(
        handler: MethodCallHandler,
        pirCall: PIRCall,
        callee: PIRFunction,
        factMapper: PIRMethodCallFactMapper,
    ): MethodCallHandler? = when (handler) {
        is MethodCallHandler.ZeroToZeroHandler -> handler
        is MethodCallHandler.ZeroToFactHandler -> {
            val newBase: AccessPathBase = factMapper.offsetEnter(pirCall, callee, handler.startFactBase) ?: return null
            MethodCallHandler.ZeroToFactHandler(handler.currentEdge, newBase)
        }
        is MethodCallHandler.FactToFactHandler -> {
            val newBase: AccessPathBase = factMapper.offsetEnter(pirCall, callee, handler.startFactBase) ?: return null
            MethodCallHandler.FactToFactHandler(handler.currentEdge, newBase)
        }
        is MethodCallHandler.NDFactToFactHandler -> {
            val newBase: AccessPathBase = factMapper.offsetEnter(pirCall, callee, handler.startFactBase) ?: return null
            MethodCallHandler.NDFactToFactHandler(handler.currentEdge, newBase)
        }
    }

    override fun resolvedMethodCalls(
        callerContext: MethodAnalysisContext,
        callExpr: CommonCallExpr,
        location: CommonInst,
    ): List<MethodCallResolutionResult> {
        val pirCall = location as PIRCall
        val callees = callResolver.resolve(pirCall).realCallees()
        if (callees.isEmpty()) return listOf(MethodCallResolutionResult.ResolutionFailure)
        return callees.map {
            MethodCallResolutionResult.ResolvedMethod(MethodWithContext(it, EmptyMethodContext))
        }
    }
}
