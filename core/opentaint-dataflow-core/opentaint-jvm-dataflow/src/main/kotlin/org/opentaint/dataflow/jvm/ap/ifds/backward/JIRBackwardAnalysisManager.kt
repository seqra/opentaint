package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
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
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.graph.reversed
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLambdaTracker
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature.JIRLambdaClass
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.mkAccessPath
import org.opentaint.dataflow.util.getOrCreate
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.PredefinedPrimitives
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.api.jvm.ext.cfg.locals
import org.opentaint.util.analysis.ApplicationGraph

class JIRBackwardAnalysisManager private constructor(
    private val forward: JIRAnalysisManager,
    private val analysisEndMethods: Set<CommonMethod>,
    val rules: JIRBackwardTaintRulesProvider,
) : JIRAnalysisManager(forward.cp, forward.rootRefManager, rules, forward.externalMethodTracker, forward.params) {
    constructor(forward: JIRAnalysisManager, analysisEndMethods: Set<CommonMethod>) :
        this(forward, analysisEndMethods, JIRBackwardTaintRulesProvider(forward.taintConfig))

    override val relevantRuleIds get() = forward.relevantRuleIds

    val starUnroller = JIRBackwardStarUnroller(cp)
    private val nonExitingStarts = JIRBackwardNonExitingStarts()

    private val forwardContexts by lazy { forward.contexts.groupBy { it.methodEntryPoint.method } }

    override fun getMethodCallResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        unitResolver: UnitResolver<CommonMethod>,
        runner: TaintAnalysisUnitRunner
    ): JIRMethodCallResolver = super.getMethodCallResolver(graph.reversed, unitResolver, runner)

    override fun getMethodAnalysisContext(
        methodEntryPoint: MethodEntryPoint,
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        callResolver: MethodCallResolver,
        taintAnalysisContext: TaintAnalysisContext,
        contextForEmptyMethod: MethodAnalysisContext?
    ): MethodAnalysisContext {
        val forwardGraph = graph.reversed
        val forwardEntryPoint = forwardGraph.methodGraph(methodEntryPoint.method).entryPoints().first()
        val forwardContext = super.getMethodAnalysisContext(
            methodEntryPoint.copy(statement = forwardEntryPoint), forwardGraph,
            callResolver, taintAnalysisContext, contextForEmptyMethod
        ) as JIRMethodAnalysisContext

        return JIRBackwardMethodAnalysisContext(forwardContext, methodEntryPoint).also {
            addForwardLambdas(it)
            contexts.add(it)
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
            graph.methodGraph(method).entryPoints().toList() + nonExitingStarts.resolve(graph.reversed.methodGraph(method))
    }

    override fun getMethodStartFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext
    ): MethodStartFlowFunction {
        analysisContext as JIRBackwardMethodAnalysisContext
        val entryPoint = analysisContext.methodEntryPoint
        val zeroOnly = producesExceptionalControlFlow(entryPoint.statement) ||
            nonExitingStarts.isNonExitingStart(entryPoint.method, entryPoint.statement)
        val endDemands = if (zeroOnly) emptyList() else endDemands(apManager, entryPoint.method as JIRMethod)
        return JIRBackwardMethodStartFlowFunction(apManager, analysisContext, zeroOnly, endDemands)
    }

    private val endRequirements: List<Pair<PositionAccess, TaintMarkAccessor>> by lazy {
        val requirements = hashSetOf<Pair<PositionAccess, TaintMarkAccessor>>()
        for ((method, contexts) in forwardContexts) {
            method as JIRMethod
            val sinks = mutableListOf<TaintConfigurationSink>()
            contexts.mapTo(hashSetOf()) { it.methodEntryPoint.statement }.forEach { enter ->
                sinks += forward.taintConfig.sinkRulesForMethodEntry(method, enter, fact = null)
            }
            for (inst in method.instList) {
                inst.callExpr?.let { sinks += forward.taintConfig.sinkRulesForMethod(it.method.method, inst, fact = null) }
                if (inst is JIRReturnInst) {
                    sinks += forward.taintConfig.sinkRulesForMethodExit(method, inst, fact = null, initialFacts = emptySet())
                }
            }
            sinks.mapNotNullTo(requirements) { sink ->
                JIRBackwardTaintRulesProvider.endRequirement(sink)?.let { it.position.resolveAp() to TaintMarkAccessor(it.mark.name) }
            }
        }
        requirements.toList()
    }

    private fun endDemands(apManager: ApManager, method: JIRMethod): List<FinalFactAp> {
        if (endRequirements.isEmpty()) return emptyList()

        val analysisEnd = method in analysisEndMethods
        val bases = method.instList.locals.mapNotNullTo(hashSetOf()) { local ->
            MethodFlowFunctionUtils.accessPathBase(local)?.takeIf { it is AccessPathBase.LocalVar || analysisEnd }
        }
        if (analysisEnd) {
            method.parameters.indices.mapTo(bases) { AccessPathBase.Argument(it) }
            if (!method.isStatic) bases += AccessPathBase.This
            if (method.returnType.typeName != PredefinedPrimitives.Void) bases += AccessPathBase.Return
        }

        return endRequirements.flatMap { (position, mark) ->
            val fact = apManager.mkAccessPath(position, ExclusionSet.Universe, mark)
            when {
                fact.base !is AccessPathBase.ClassStatic -> bases.map { fact.rebase(it) }
                analysisEnd -> listOf(fact)
                else -> emptyList()
            }
        }
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
    ): MethodSequentFlowFunction =
        JIRBackwardMethodSequentFlowFunction(apManager, analysisContext as JIRBackwardMethodAnalysisContext, currentInst as JIRInst)

    override fun getMethodCallFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst,
        generateTrace: Boolean
    ): MethodCallFlowFunction = JIRBackwardMethodCallFlowFunction(
        apManager, analysisContext as JIRBackwardMethodAnalysisContext,
        returnValue as JIRImmediate?, callExpr as JIRCallExpr, statement as JIRInst
    )

    override fun getMethodCallSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst
    ): MethodCallSummaryHandler =
        JIRBackwardMethodCallSummaryHandler(statement as JIRInst, analysisContext as JIRMethodAnalysisContext, apManager)

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
