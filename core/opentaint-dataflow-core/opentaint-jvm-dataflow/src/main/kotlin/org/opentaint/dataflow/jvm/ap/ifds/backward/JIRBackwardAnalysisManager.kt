package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.BackwardRunResult
import org.opentaint.dataflow.ap.ifds.BackwardSinkOccurrence
import org.opentaint.dataflow.ap.ifds.BackwardTaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
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
import org.opentaint.ir.api.jvm.ext.cfg.locals
import org.opentaint.util.analysis.ApplicationGraph

class JIRBackwardAnalysisManager(
    private val forward: JIRAnalysisManager,
) : JIRAnalysisManager(forward.cp, forward.rootRefManager, forward.taintConfig, forward.externalMethodTracker, forward.params) {
    override val relevantRuleIds get() = forward.relevantRuleIds

    override fun createBackwardAnalysisManager(): BackwardTaintAnalysisManager = this

    val findings = JIRBackwardFindingTracker()
    val starUnroller = JIRBackwardStarUnroller(cp)
    private val nonExitingStarts = JIRBackwardNonExitingStarts()

    private val forwardContexts by lazy { forward.contexts.groupBy { it.methodEntryPoint.method } }

    @Volatile
    private var analysisEndMethods: Set<CommonMethod> = emptySet()

    override fun prepareBackwardRun(analysisEndMethods: Set<CommonMethod>, restrictedTo: Set<BackwardSinkOccurrence>?) {
        this.analysisEndMethods = analysisEndMethods
        findings.configureRun(restrictedTo)
    }

    override fun backwardRunResult(): BackwardRunResult {
        val restricted = findings.restrictedTo
        val seededSinks = findings.seededSinks()

        val seeded = hashMapOf<BackwardSinkOccurrence, MutableSet<TaintMarkAccessor>>()
        seededSinks.forEach { seeded.getOrPut(it.occurrence, ::hashSetOf).addAll(it.demandedMarks()) }

        val vulnerable = hashMapOf<BackwardSinkOccurrence, MethodEntryPoint>()
        findings.vulnerableSinks(checkEndRequirements = restricted != null).forEach {
            vulnerable.putIfAbsent(it.occurrence, it.methodEntryPoint)
        }

        val exact = restricted?.let { it.size <= 1 }
            ?: (seeded.size <= 1 && seededSinks.all { it.endRequirement == null } && !findings.hasZeroEdgeOnlySinks)
        return BackwardRunResult(seeded, vulnerable, exact)
    }

    override fun selectPhase(phase: Phase) {
        findings.reset()
        super.selectPhase(phase)
    }

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

    private fun endDemands(apManager: ApManager, method: JIRMethod): List<FinalFactAp> {
        if (!findings.hasEndRequirementTargets) return emptyList()
        val occurrences = findings.restrictedTo ?: return emptyList()

        val requirements = occurrences.mapNotNull {
            JIRBackwardEndRequirement.of(apManager, factTypeChecker, it.rule as TaintConfigurationSink, it.statement as JIRInst)
        }
        if (requirements.isEmpty()) return emptyList()

        val analysisEnd = method in analysisEndMethods
        val bases = method.instList.locals.mapNotNullTo(hashSetOf()) { local ->
            MethodFlowFunctionUtils.accessPathBase(local)?.takeIf { it is AccessPathBase.LocalVar || analysisEnd }
        }
        if (analysisEnd) {
            method.parameters.indices.mapTo(bases) { AccessPathBase.Argument(it) }
            if (!method.isStatic) bases += AccessPathBase.This
            if (method.returnType.typeName != PredefinedPrimitives.Void) bases += AccessPathBase.Return
        }

        return requirements.flatMap { requirement ->
            when {
                !requirement.analysisEndOnly -> bases.map { requirement.fact.rebase(it) }
                analysisEnd -> listOf(requirement.fact)
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
