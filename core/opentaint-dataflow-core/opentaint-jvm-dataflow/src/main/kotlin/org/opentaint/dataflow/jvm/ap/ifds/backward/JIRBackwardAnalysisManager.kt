package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSideEffectSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodStartPrecondition
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.graph.reversed
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLambdaTracker
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature.JIRLambdaClass
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallSummaryHandler
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.util.getOrCreate
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.util.analysis.ApplicationGraph

class JIRBackwardAnalysisManager private constructor(
    private val forward: JIRAnalysisManager,
    private val delegate: JIRAnalysisManager,
) : TaintAnalysisManager by delegate {
    constructor(forward: JIRAnalysisManager) : this(
        forward,
        JIRAnalysisManager(
            forward.cp, forward.rootRefManager, forward.taintConfig,
            forward.externalMethodTracker, forward.params, forward.relevantRuleIds
        )
    )

    private val forwardContexts by lazy { forward.contexts.groupBy { it.methodEntryPoint.method } }

    override fun getMethodCallResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        unitResolver: UnitResolver<CommonMethod>,
        runner: TaintAnalysisUnitRunner
    ): MethodCallResolver = delegate.getMethodCallResolver(graph.reversed, unitResolver, runner)

    override fun getMethodAnalysisContext(
        methodEntryPoint: MethodEntryPoint,
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        callResolver: MethodCallResolver,
        taintAnalysisContext: TaintAnalysisContext,
        contextForEmptyMethod: MethodAnalysisContext?
    ): MethodAnalysisContext {
        val forwardGraph = graph.reversed
        val forwardEntryPoint = forwardGraph.methodGraph(methodEntryPoint.method).entryPoints().first()
        val forwardContext = delegate.getMethodAnalysisContext(
            methodEntryPoint.copy(statement = forwardEntryPoint), forwardGraph,
            callResolver, taintAnalysisContext, contextForEmptyMethod
        ) as JIRMethodAnalysisContext

        val forwardTaint = JIRTaintAnalysisContext(
            taintAnalysisContext.taintSinkTracker, delegate.taintConfig, delegate.externalMethodTracker, delegate.relevantRuleIds
        )

        return JIRMethodAnalysisContext(
            delegate,
            forwardContext.refManager,
            methodEntryPoint,
            forwardContext.factTypeChecker,
            forwardContext.localVariableReachability,
            forwardContext.aliasAnalysis,
            JIRBackwardTaintAnalysisContext(forwardTaint, delegate.taintConfig),
            JIRBackwardMethodCallFactMapper,
        ).also {
            addForwardLambdas(it)
            delegate.contexts.add(it)
        }
    }

    private fun addForwardLambdas(context: JIRMethodAnalysisContext) {
        for (forwardContext in forwardContexts[context.methodEntryPoint.method].orEmpty()) {
            for ((idx, tracker) in forwardContext.lambdaCallResolution) {
                val lambdas = context.lambdaCallResolution.getOrCreate(idx) { JIRLambdaTracker.LambdaTracker(tracker.method) }
                tracker.forEachRegisteredLambda(object : JIRLambdaTracker.LambdaSubscriber {
                    override fun newLambda(method: JIRMethod, lambdaClass: JIRLambdaClass) = lambdas.addLambda(lambdaClass)
                })
            }
        }
    }

    override fun getMethodEntrypointResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
    ): MethodEntrypointResolver = object : MethodEntrypointResolver {
        override fun resolveEntryPoints(method: CommonMethod, context: MethodContext): List<CommonInst> =
            graph.methodGraph(method).entryPoints().toList()
    }

    override fun getMethodInstGraph(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        analysisContext: MethodAnalysisContext,
        method: CommonMethod
    ): MethodInstGraph = delegate.getMethodInstGraph(JIRBackwardExitWiringGraph(graph.reversed).reversed, analysisContext, method)

    override fun getMethodStartFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext
    ): MethodStartFlowFunction {
        analysisContext as JIRMethodAnalysisContext
        val entryPoint = analysisContext.methodEntryPoint
        val zeroOnly = producesExceptionalControlFlow(entryPoint.statement)
        return JIRBackwardMethodStartFlowFunction(apManager, analysisContext, zeroOnly)
    }

    override fun getMethodStartPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext
    ): MethodStartPrecondition = JIRBackwardMethodStartPrecondition

    override fun getMethodSequentPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst
    ): MethodSequentPrecondition = JIRBackwardMethodSequentPrecondition

    override fun getMethodCallPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst
    ): MethodCallPrecondition = JIRBackwardMethodCallPrecondition

    override fun getMethodSequentFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst,
        generateTrace: Boolean
    ): MethodSequentFlowFunction {
        analysisContext as JIRMethodAnalysisContext
        currentInst as JIRInst
        return analysisContext.cachedSequentFF(currentInst.location.index, generateTrace = false) {
            JIRBackwardMethodSequentFlowFunction(
                apManager, analysisContext, analysisContext.taint as JIRBackwardTaintAnalysisContext, currentInst
            )
        }
    }

    override fun getMethodCallFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst,
        generateTrace: Boolean
    ): MethodCallFlowFunction = JIRBackwardMethodCallFlowFunction(
        apManager, analysisContext as JIRMethodAnalysisContext,
        returnValue as JIRImmediate?, callExpr as JIRCallExpr, statement as JIRInst
    )

    override fun getMethodCallSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst
    ): MethodCallSummaryHandler = JIRBackwardMethodCallSummaryHandler(
        JIRMethodCallSummaryHandler(statement as JIRInst, analysisContext as JIRMethodAnalysisContext, apManager, withCallAliases = false)
    )

    override fun getMethodSideEffectSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst,
        runner: AnalysisRunner
    ): MethodSideEffectSummaryHandler = object : MethodSideEffectSummaryHandler {}

    override fun isReachable(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        base: AccessPathBase,
        statement: CommonInst
    ): Boolean = true

    override fun isValidMethodExitFact(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        fact: FinalFactAp
    ): Boolean = JIRBackwardMethodCallFactMapper.isValidMethodExitFact(fact)
}
