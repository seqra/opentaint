package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodEdgePostProcessor
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSideEffectSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodStartPrecondition
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.graph.reversed
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodContextSerializer
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManagerBase
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSummaryEdgeProcessor
import org.opentaint.dataflow.jvm.ap.ifds.jIRDowncast
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.SelectedTaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedQueue

class JIRBackwardAnalysisManager(
    cp: JIRClasspath,
    refManager: RefManager,
    val taintConfig: TaintRulesProvider,
    val externalMethodTracker: ExternalMethodTracker? = null,
    override val params: JIRAnalysisManager.Params = JIRAnalysisManager.Params(),
) : JIRLanguageManager(cp), TaintAnalysisManager, JIRAnalysisManagerBase {
    private val refManager = refManager.softRefManager("JIRBackwardAnalysisManager")
    private val phaseTaintConfig = SelectedTaintRulesProvider(taintConfig)

    override val factTypeChecker = JIRFactTypeChecker(cp)

    val findings = JIRBackwardFindingTracker()

    private val relevantRuleIds = ConcurrentHashMap.newKeySet<String>()
    private val contexts = ConcurrentLinkedQueue<JIRBackwardMethodAnalysisContext>()

    private var currentPhase: Phase = Phase.Prescan
    override val phase: Phase get() = currentPhase

    override fun selectPhase(phase: Phase) {
        currentPhase = phase
        contexts.forEach { it.resetAnalysisCache() }
        findings.reset()
        when (phase) {
            Phase.Prescan -> phaseTaintConfig.select(null)
            Phase.ShallowScan -> {
                phaseTaintConfig.selectRules(relevantRuleIds)
                phaseTaintConfig.select(null)
            }
            is Phase.FullScan -> {
                phaseTaintConfig.selectRules(relevantRuleIds)
                phaseTaintConfig.select(phase.actionableRules)
            }
        }
    }

    override fun getMethodCallResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        unitResolver: UnitResolver<CommonMethod>,
        runner: TaintAnalysisUnitRunner
    ): JIRMethodCallResolver {
        jIRDowncast<JApplicationGraph>(graph.reversed)
        jIRDowncast<JIRUnitResolver>(unitResolver)

        val jIRCallResolver = JIRCallResolver(cp, unitResolver)
        return JIRMethodCallResolver(jIRCallResolver, runner, externalMethodTracker)
    }

    override fun getMethodAnalysisContext(
        methodEntryPoint: MethodEntryPoint,
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        callResolver: MethodCallResolver,
        taintAnalysisContext: TaintAnalysisContext,
        contextForEmptyMethod: MethodAnalysisContext?
    ): MethodAnalysisContext {
        val entryPointStatement = methodEntryPoint.statement
        jIRDowncast<JIRInst>(entryPointStatement)
        val forwardGraph = graph.reversed
        jIRDowncast<JApplicationGraph>(forwardGraph)
        callResolver as JIRMethodCallResolver

        val backwardContextForEmptyMethod = contextForEmptyMethod as? JIRBackwardMethodAnalysisContext

        val method = entryPointStatement.location.method
        val forwardEntryPoint = backwardContextForEmptyMethod?.forwardEntryPoint
            ?: forwardGraph.methodGraph(method).entryPoints().firstOrNull()

        val localVariableReachability = backwardContextForEmptyMethod?.localVariableReachability
            ?: JIRLocalVariableReachability(method, forwardGraph, this)

        val cancellation = callResolver.runner.manager.cancellation

        val aliasAnalysisParams = params.aliasAnalysisParams
        val aliasAnalysis = if (aliasAnalysisParams.useAliasAnalysis && forwardEntryPoint != null) {
            backwardContextForEmptyMethod?.aliasAnalysis
                ?: JIRLocalAliasAnalysis(
                    forwardEntryPoint, forwardGraph, callResolver.callResolver,
                    taintConfig,
                    localVariableReachability, cancellation, this, aliasAnalysisParams
                )
        } else {
            null
        }

        val taintContext = JIRTaintAnalysisContext(
            taintAnalysisContext.taintSinkTracker, phaseTaintConfig, externalMethodTracker, relevantRuleIds
        )

        return JIRBackwardMethodAnalysisContext(
            this,
            refManager,
            methodEntryPoint,
            factTypeChecker,
            localVariableReachability,
            aliasAnalysis,
            taintContext,
            forwardEntryPoint,
            findings,
        ).also {
            contexts.add(it)
        }
    }

    override fun getMethodInstGraph(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        analysisContext: MethodAnalysisContext,
        method: CommonMethod
    ): MethodInstGraph = MethodInstGraph.build(this, graph, method)

    override fun getMethodEntrypointResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
    ): MethodEntrypointResolver = JIRBackwardMethodEntrypointResolver(graph)

    override fun getMethodStartFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext
    ): MethodStartFlowFunction {
        jIRDowncast<JIRBackwardMethodAnalysisContext>(analysisContext)
        val exceptionalExit = producesExceptionalControlFlow(analysisContext.methodEntryPoint.statement)
        return JIRBackwardMethodStartFlowFunction(apManager, analysisContext, exceptionalExit)
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

    override fun getMethodSequentFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst,
        generateTrace: Boolean
    ): MethodSequentFlowFunction {
        jIRDowncast<JIRInst>(currentInst)
        jIRDowncast<JIRBackwardMethodAnalysisContext>(analysisContext)
        return JIRBackwardMethodSequentFlowFunction(apManager, analysisContext, currentInst)
    }

    override fun getMethodCallFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst,
        generateTrace: Boolean
    ): MethodCallFlowFunction {
        jIRDowncast<JIRImmediate?>(returnValue)
        jIRDowncast<JIRCallExpr>(callExpr)
        jIRDowncast<JIRInst>(statement)
        jIRDowncast<JIRBackwardMethodAnalysisContext>(analysisContext)
        return JIRBackwardMethodCallFlowFunction(apManager, analysisContext, returnValue, callExpr, statement)
    }

    override fun getMethodCallSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst
    ): MethodCallSummaryHandler {
        jIRDowncast<JIRInst>(statement)
        jIRDowncast<JIRBackwardMethodAnalysisContext>(analysisContext)
        return JIRBackwardMethodCallSummaryHandler(statement, analysisContext)
    }

    override fun getMethodSideEffectSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst,
        runner: AnalysisRunner
    ): MethodSideEffectSummaryHandler = JIRBackwardMethodSideEffectHandler

    override fun getMethodCallPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst
    ): MethodCallPrecondition = JIRBackwardMethodCallPrecondition

    override fun getEdgePostProcessor(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        graph: MethodInstGraph,
        statement: CommonInst,
    ): MethodEdgePostProcessor {
        jIRDowncast<JIRBackwardMethodAnalysisContext>(analysisContext)
        jIRDowncast<JIRInst>(statement)
        return JIRMethodSummaryEdgeProcessor(analysisContext, graph, this, statement)
    }

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

    override val methodContextSerializer = JIRMethodContextSerializer(cp)

    override fun onInstructionReached(inst: CommonInst) {
    }
}
