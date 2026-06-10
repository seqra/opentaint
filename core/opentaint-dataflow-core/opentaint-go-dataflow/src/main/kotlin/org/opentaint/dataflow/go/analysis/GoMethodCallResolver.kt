package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner.LambdaResolvedEvent
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver.MethodCallResolutionResult
import org.opentaint.dataflow.call.tryExtractCallTypeInfo
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoCallResolver
import org.opentaint.dataflow.go.GoClosureTracker
import org.opentaint.dataflow.go.GoClosureTracker.ClosureTracker
import org.opentaint.dataflow.util.getOrCreate
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRFunctionValueExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.ext.findFunctionByFullName
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.type.GoIRCallMode

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
    ) = resolveGoMethodCall(
        callerContext as GoMethodAnalysisContext,
        callExpr as GoCallExpr,
        location as GoIRInst,
        handler,
        failureHandler
    )

    fun resolveGoMethodCall(
        callerContext: GoMethodAnalysisContext,
        callExpr: GoCallExpr,
        location: GoIRInst,
        handler: MethodAnalyzer.MethodCallHandler,
        failureHandler: MethodAnalyzer.MethodCallResolutionFailureHandler,
    ) {
        val analyzer = runner.getMethodAnalyzer(callerContext.methodEntryPoint)
        val resolved = callResolver.resolve(callExpr.callInfo, location)

        if (!resolved.isNullOrEmpty()) {
            for (callee in resolved) {
                analyzer.handleResolvedMethodCall(MethodWithContext(callee, EmptyMethodContext), handler)
            }
            return
        }

        analyzer.handleMethodCallResolutionFailure(callExpr, failureHandler)

        if (callExpr.callInfo.mode == GoIRCallMode.DYNAMIC) {
            resolveDynamicClosure(callerContext, location, handler, analyzer)
        }
    }

    data object ClosureCreationFlowFunction {
        fun handle(inst: GoIRInst, body: (AccessPathBase, List<Accessor>) -> Unit) {
            val expr = (inst as? GoIRAssignInst)?.expr ?: return

            if (expr is GoIRMakeClosureExpr) {
                val base = AccessPathBase.LocalVar(inst.register.index)
                body(base, listOf(TypeInfoGroupAccessor, TypeInfoAccessor(expr.fn.fullName)))
            }

            if (expr is GoIRFunctionValueExpr) {
                val base = AccessPathBase.LocalVar(inst.register.index)
                body(base, listOf(TypeInfoGroupAccessor, TypeInfoAccessor(expr.function.fullName)))
            }
        }
    }

    private fun resolveDynamicClosure(
        callerContext: GoMethodAnalysisContext,
        location: GoIRInst,
        handler: MethodAnalyzer.MethodCallHandler,
        analyzer: MethodAnalyzer,
    ) {
        val locationIdx = location.location.index
        val tracker = callerContext.closureCallResolution.getOrCreate(locationIdx) {
            ClosureTracker()
        }

        val subscription = ClosureSubscription(runner, callerContext.methodEntryPoint, handler)
        tracker.addSubscriber(subscription)

        tracker.tryExtractClosureName(handler, analyzer)
    }

    private fun ClosureTracker.tryExtractClosureName(
        handler: MethodAnalyzer.MethodCallHandler,
        analyzer: MethodAnalyzer
    ) = tryExtractCallTypeInfo(handler, analyzer, { it == AccessPathBase.This }) { typeInfo ->
        val closureFn = callResolver.cp.findFunctionByFullName(typeInfo.typeName)
            ?: return@tryExtractCallTypeInfo

        addValue(closureFn)
    }

    override fun resolvedMethodCalls(
        callerContext: MethodAnalysisContext,
        callExpr: CommonCallExpr,
        location: CommonInst,
    ) = resolvedGoMethodCalls(
        callerContext as GoMethodAnalysisContext,
        callExpr as GoCallExpr,
        location as GoIRInst
    )

    private fun resolvedGoMethodCalls(
        callerContext: GoMethodAnalysisContext,
        callExpr: GoCallExpr,
        location: GoIRInst,
    ): List<MethodCallResolutionResult> {
        val resolved = callResolver.resolve(callExpr.callInfo, location)

        if (!resolved.isNullOrEmpty()) {
            return resolved.map {
                MethodCallResolutionResult.ResolvedMethod(MethodWithContext(it, EmptyMethodContext))
            }
        }

        val results = mutableListOf<MethodCallResolutionResult>(MethodCallResolutionResult.ResolutionFailure)

        if (callExpr.callInfo.mode == GoIRCallMode.DYNAMIC) {
            val locationIdx = location.location.index
            val tracker = callerContext.closureCallResolution.get(locationIdx)
            tracker?.forEachRegisteredValue(
                object : GoClosureTracker.ClosureSubscriber {
                    override fun handle(key: Unit, value: GoIRFunction) {
                        results += MethodCallResolutionResult.ResolvedMethod(
                            MethodWithContext(value, EmptyMethodContext)
                        )
                    }
                }
            )
        }

        return results
    }

    private data class ClosureSubscription(
        private val runner: TaintAnalysisUnitRunner,
        private val callerEntryPoint: MethodEntryPoint,
        private val handler: MethodAnalyzer.MethodCallHandler,
    ) : GoClosureTracker.ClosureSubscriber {
        override fun handle(key: Unit, value: GoIRFunction) {
            runner.addResolvedLambdaEvent(
                LambdaResolvedEvent(
                    callerEntryPoint,
                    handler,
                    MethodWithContext(value, EmptyMethodContext),
                )
            )
        }
    }
}
