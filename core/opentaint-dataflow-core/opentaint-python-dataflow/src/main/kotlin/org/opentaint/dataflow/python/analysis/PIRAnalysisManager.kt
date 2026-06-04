package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
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
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.python.PIRCallResolver
import org.opentaint.dataflow.python.PIRLanguageManager
import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.dataflow.python.rules.PIRTaintAnalysisContext
import org.opentaint.dataflow.python.rules.PIRTaintConfiguration
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.util.analysis.ApplicationGraph

class PIRAnalysisManager(
    cp: PIRClasspath,
    val taintRules: PIRTaintConfiguration,
) : PIRLanguageManager(cp), TaintAnalysisManager {
    override val factTypeChecker: FactTypeChecker = FactTypeChecker.Dummy
    private val pirApplicationGraph = PIRApplicationGraph(cp)
    private val pirCallResolver = PIRCallResolver(cp, pirApplicationGraph)

    override fun getMethodAnalysisContext(
        methodEntryPoint: MethodEntryPoint,
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        callResolver: MethodCallResolver,
        taintAnalysisContext: TaintAnalysisContext,
        contextForEmptyMethod: MethodAnalysisContext?,
    ): MethodAnalysisContext {
        val method = methodEntryPoint.method as PIRFunction
        val taintCtx = PIRTaintAnalysisContext(taintAnalysisContext.taintSinkTracker)
        return PIRMethodAnalysisContext(methodEntryPoint, method, taintCtx, taintRules)
    }

    override fun getMethodInstGraph(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        analysisContext: MethodAnalysisContext,
        method: CommonMethod
    ): MethodInstGraph = MethodInstGraph.build(this, graph, method)

    override fun getMethodEntrypointResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>
    ): MethodEntrypointResolver {
        return PIRMethodEntrypointResolver(graph as PIRApplicationGraph)
    }

    override fun getMethodCallResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        unitResolver: UnitResolver<CommonMethod>,
        runner: TaintAnalysisUnitRunner,
    ): MethodCallResolver =
        PIRMethodCallResolver(pirCallResolver, runner)

    override fun getMethodStartFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
    ): MethodStartFlowFunction {
        val ctx = analysisContext as PIRMethodAnalysisContext
        return PIRMethodStartFlowFunction(ctx, apManager)
    }

    override fun getMethodStartPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
    ): MethodStartPrecondition = NoOpStartPrecondition

    override fun getMethodSequentPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst,
    ): MethodSequentPrecondition = NoOpSequentPrecondition

    override fun getMethodSequentFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst,
        generateTrace: Boolean,
    ): MethodSequentFlowFunction {
        val ctx = analysisContext as PIRMethodAnalysisContext
        return PIRMethodSequentFlowFunction(
            currentInst as PIRInstruction, ctx, apManager, pirCallResolver
        )
    }

    override fun getMethodCallFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst,
        generateTrace: Boolean,
    ): MethodCallFlowFunction {
        val ctx = analysisContext as PIRMethodAnalysisContext
        val pirCall = statement as PIRCall
        return PIRMethodCallFlowFunction(
            pirCall, ctx.method, ctx, apManager, returnValue, pirCallResolver
        )
    }

    override fun getMethodCallPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst,
    ): MethodCallPrecondition = NoOpCallPrecondition

    override fun getMethodCallSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst,
    ): MethodCallSummaryHandler {
        val ctx = analysisContext as PIRMethodAnalysisContext
        return PIRMethodCallSummaryHandler(
            statement as PIRCall, ctx, pirCallResolver, factTypeChecker
        )
    }

    override fun getMethodSideEffectSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst,
        runner: AnalysisRunner,
    ): MethodSideEffectSummaryHandler =
        PIRMethodSideEffectSummaryHandler()

    override fun isReachable(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        base: AccessPathBase,
        statement: CommonInst,
    ): Boolean = true // TODO

    override fun isValidMethodExitFact(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        fact: FinalFactAp,
    ): Boolean = when (fact.base) {
        is AccessPathBase.LocalVar -> false
        is AccessPathBase.Return -> true
        is AccessPathBase.Argument -> true  // Arguments can flow back (aliased)
        is AccessPathBase.ClassStatic -> true
        else -> false
    }

    override fun onInstructionReached(inst: CommonInst) {
        // No-op
    }
}

// --- No-op preconditions for minimal prototype ---

private object NoOpStartPrecondition : MethodStartPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<TaintRulePrecondition.Source> = emptyList()
}

private object NoOpSequentPrecondition : MethodSequentPrecondition {
    override fun factPrecondition(fact: InitialFactAp): Set<MethodSequentPrecondition.SequentPrecondition> =
        setOf(MethodSequentPrecondition.SequentPrecondition.Unchanged)
}

private object NoOpCallPrecondition : MethodCallPrecondition {
    override fun factPrecondition(fact: InitialFactAp): List<MethodCallPrecondition.CallPrecondition> =
        listOf(MethodCallPrecondition.CallPrecondition.Unchanged)

    override fun factPreconditionResolutionFailure(
        fact: InitialFactAp,
        startFactBase: AccessPathBase
    ): List<MethodCallPrecondition.CallPreconditionFact.CallFailurePreconditionFact> =
        emptyList()

    override fun resolvePassRuleCondition(
        precondition: PassRuleCondition,
        edges: MethodAnalyzerEdges
    ): List<MethodCallPrecondition.PassRuleConditionFacts> =
        emptyList()
}