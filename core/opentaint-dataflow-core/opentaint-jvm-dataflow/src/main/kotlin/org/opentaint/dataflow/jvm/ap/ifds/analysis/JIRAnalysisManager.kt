package org.opentaint.dataflow.jvm.ap.ifds.analysis

import mu.KLogger
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.AnalysisRunner
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.ir.api.jvm.ext.allSuperHierarchySequence
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.dataflow.jvm.ap.ifds.JIRArgumentTypeMethodContext
import org.opentaint.dataflow.jvm.ap.ifds.JIRInstanceTypeMethodContext
import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.CombinedMethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager
import org.opentaint.dataflow.ap.ifds.TaintAnalysisManager.Phase
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunner
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyFinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodAnalysisContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodEdgePostProcessor
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSideEffectSummaryHandler
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction
import org.opentaint.dataflow.ap.ifds.taint.ActionableRules
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodStartPrecondition
import org.opentaint.dataflow.graph.MethodInstGraph
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLambdaTracker
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodContextSerializer
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature
import org.opentaint.dataflow.jvm.ap.ifds.jIRDowncast
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.taint.SelectedTaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.trace.JIRMethodCallPrecondition
import org.opentaint.dataflow.jvm.ap.ifds.trace.JIRMethodSequentPrecondition
import org.opentaint.dataflow.jvm.ap.ifds.trace.JIRMethodStartPrecondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRExprVisitor
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstVisitor
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.ir.api.jvm.ext.findMethodOrNull
import org.opentaint.jvm.graph.JApplicationGraph
import org.opentaint.util.analysis.ApplicationGraph
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedQueue

class JIRAnalysisManager(
    cp: JIRClasspath,
    refManager: RefManager,
    val taintConfig: TaintRulesProvider,
    val externalMethodTracker: ExternalMethodTracker? = null,
    private val params: Params = Params(),
) : JIRLanguageManager(cp), TaintAnalysisManager {
    override val supportsForwardActionableRuleFallback: Boolean = true

    override fun overApproximateMethodContext(
        method: MethodWithContext,
        contextIndependentFact: Boolean,
    ): MethodWithContext {
        if (currentPhase !is Phase.ShallowScan) return method
        if (!contextIndependentFact) return method
        if (method.ctx is EmptyMethodContext || method.ctx.containsLambdaConstraint()) return method
        return method.copy(ctx = EmptyMethodContext)
    }

    private val contextBoundFunctionTypes = ConcurrentHashMap<JIRClassOrInterface, Boolean>()

    private fun MethodContext.containsLambdaConstraint(): Boolean = when (this) {
        is JIRInstanceTypeMethodContext -> typeConstraint.type.isContextBoundFunction()
        is JIRArgumentTypeMethodContext -> typeConstraint.type.isContextBoundFunction()
        is CombinedMethodContext -> first.containsLambdaConstraint() || second.containsLambdaConstraint()
        else -> false
    }

    private fun JIRClassOrInterface.isContextBoundFunction(): Boolean =
        contextBoundFunctionTypes.computeIfAbsent(this) { type ->
            type is LambdaAnonymousClassFeature.JIRLambdaClass ||
                (sequenceOf(type) + type.allSuperHierarchySequence).any { superType ->
                    superType.name.startsWith("kotlin.jvm.functions.Function") ||
                        superType.name.startsWith("kotlin.coroutines.SuspendFunction") ||
                        superType.name.startsWith("java.util.function.")
                }
        }

    override fun relevantForwardActionableRules(
        rules: ActionableRules,
        uncoveredSinkRules: Set<CommonTaintConfigurationItem>,
    ): ActionableRules {
        if (uncoveredSinkRules.isEmpty()) return rules

        val sinkRuleIds = hashSetOf<String>()
        for (rule in uncoveredSinkRules) {
            val ruleId = (rule as? TaintConfigurationItem)?.serializedId ?: return rules
            sinkRuleIds += ruleId
        }

        val candidateRuleIds = rules.values
            .asSequence()
            .flatMap { it.keys.asSequence() }
            .mapNotNullTo(hashSetOf()) { (it as? TaintConfigurationItem)?.serializedId }
        candidateRuleIds += sinkRuleIds

        val relevantRuleIds = taintConfig.relevantRuleIds(candidateRuleIds) ?: return rules
        return buildMap {
            rules.forEach { (statement, statementRules) ->
                val retainedRules = statementRules.filterTo(linkedMapOf()) { (rule, _) ->
                    val ruleId = (rule as? TaintConfigurationItem)?.serializedId
                    ruleId == null || ruleId in relevantRuleIds
                }
                if (retainedRules.isNotEmpty()) put(statement, retainedRules)
            }
        }
    }

    private object StaticFieldAccessDetector :
        JIRExprVisitor.Default<Boolean>,
        JIRInstVisitor.Default<Boolean> {
        override fun defaultVisitJIRExpr(expr: JIRExpr): Boolean =
            expr.operands.any { it.accept(this) }

        override fun defaultVisitJIRInst(inst: JIRInst): Boolean =
            inst.operands.any { it.accept(this) }

        override fun visitJIRFieldRef(value: JIRFieldRef): Boolean =
            value.field.isStatic || defaultVisitJIRExpr(value)
    }

    private class FactBaseAccessDetector(
        private val base: AccessPathBase,
    ) : JIRExprVisitor.Default<Boolean>, JIRInstVisitor.Default<Boolean> {
        override fun defaultVisitJIRExpr(expr: JIRExpr): Boolean =
            expr.operands.any { it.accept(this) }

        override fun defaultVisitJIRInst(inst: JIRInst): Boolean =
            inst.operands.any { it.accept(this) }

        override fun defaultVisitJIRValue(value: JIRValue): Boolean =
            MethodFlowFunctionUtils.accessPathBase(value) == base || defaultVisitJIRExpr(value)
    }

    private val refManager = refManager.softRefManager("JIRAnalysisManager")
    private val phaseTaintConfig = SelectedTaintRulesProvider(taintConfig)

    override val factTypeChecker = JIRFactTypeChecker(cp)

    data class Params(
        val aliasAnalysisParams: JIRLocalAliasAnalysis.Params = JIRLocalAliasAnalysis.Params(),
    )

    private val relevantRuleIds = ConcurrentHashMap.newKeySet<String>()
    private val contexts = ConcurrentLinkedQueue<JIRMethodAnalysisContext>()
    @Volatile
    private var classStaticFootprintIndex: JIRClassStaticFootprintIndex? = null

    private var currentPhase: Phase = Phase.Prescan
    val phase: Phase get() = currentPhase

    override fun selectPhase(phase: Phase) {
        currentPhase = phase
        classStaticFootprintIndex = null
        contexts.forEach { it.resetAnalysisCache() }

        when (phase) {
            is Phase.Prescan -> {
                phaseTaintConfig.select(null)
            }

            is Phase.ShallowScan -> {
                phaseTaintConfig.selectRules(relevantRuleIds)
                phaseTaintConfig.select(null)
            }

            is Phase.FullScan -> {
                phaseTaintConfig.select(phase.actionableRules)
            }
        }
    }

    override fun getMethodCallResolver(
        graph: ApplicationGraph<CommonMethod, CommonInst>,
        unitResolver: UnitResolver<CommonMethod>,
        runner: TaintAnalysisUnitRunner
    ): JIRMethodCallResolver {
        jIRDowncast<JApplicationGraph>(graph)
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
        jIRDowncast<JApplicationGraph>(graph)
        callResolver as JIRMethodCallResolver

        val jirContextForEmptyMethod = contextForEmptyMethod as? JIRMethodAnalysisContext

        val method = entryPointStatement.location.method
        val localVariableReachability = jirContextForEmptyMethod?.localVariableReachability
            ?: JIRLocalVariableReachability(method, graph, this)

        val runnerManager = callResolver.runner.manager
        val cancellation = runnerManager.cancellation

        val aliasAnalysisParams = params.aliasAnalysisParams
        val aliasAnalysis = if (aliasAnalysisParams.useAliasAnalysis) {
            jirContextForEmptyMethod?.aliasAnalysis
                ?: JIRLocalAliasAnalysis(
                    entryPointStatement, graph, callResolver.callResolver,
                    taintConfig,
                    localVariableReachability, cancellation, this, aliasAnalysisParams
                )
        } else {
            null
        }

        val taintContext = JIRTaintAnalysisContext(
            taintAnalysisContext.taintSinkTracker, phaseTaintConfig, externalMethodTracker, relevantRuleIds
        )

        return JIRMethodAnalysisContext(
            this,
            refManager,
            methodEntryPoint,
            factTypeChecker,
            localVariableReachability,
            aliasAnalysis,
            taintContext,
            callResolver.callResolver,
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
    ): MethodEntrypointResolver {
        jIRDowncast<JApplicationGraph>(graph)
        return JIRMethodEntrypointResolver(graph)
    }

    override fun getMethodStartFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext
    ): MethodStartFlowFunction {
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)
        return JIRMethodStartFlowFunction(apManager, analysisContext)
    }

    override fun getMethodStartPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext
    ): MethodStartPrecondition {
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)
        return JIRMethodStartPrecondition(apManager, analysisContext)
    }

    override fun getMethodSequentPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst
    ): MethodSequentPrecondition {
        jIRDowncast<JIRInst>(currentInst)
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)

        return JIRMethodSequentPrecondition(apManager, currentInst, analysisContext)
    }

    override fun getMethodSequentFlowFunction(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        currentInst: CommonInst,
        generateTrace: Boolean
    ): MethodSequentFlowFunction {
        jIRDowncast<JIRInst>(currentInst)
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)

        return JIRMethodSequentFlowFunction(apManager, analysisContext, currentInst, generateTrace)
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
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)

        return analysisContext.cachedCallFF(statement.location.index) {
            JIRMethodCallFlowFunction(
                apManager,
                analysisContext,
                returnValue,
                callExpr,
                statement,
                generateTrace
            )
        }
    }

    override fun getMethodCallSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst
    ): MethodCallSummaryHandler {
        jIRDowncast<JIRInst>(statement)
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)

        return analysisContext.cachedCallSH(statement.location.index) {
            JIRMethodCallSummaryHandler(statement, analysisContext, apManager)
        }
    }

    override fun getMethodSideEffectSummaryHandler(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        statement: CommonInst,
        runner: AnalysisRunner
    ): MethodSideEffectSummaryHandler {
        jIRDowncast<JIRInst>(statement)
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)

        return JIRMethodSideEffectHandler(runner)
    }

    override fun getMethodCallPrecondition(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        statement: CommonInst
    ): MethodCallPrecondition {
        jIRDowncast<JIRImmediate?>(returnValue)
        jIRDowncast<JIRCallExpr>(callExpr)
        jIRDowncast<JIRInst>(statement)
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)

        return JIRMethodCallPrecondition(
            apManager,
            analysisContext,
            returnValue,
            callExpr,
            statement
        )
    }

    override fun getEdgePostProcessor(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        graph: MethodInstGraph,
        statement: CommonInst,
    ): MethodEdgePostProcessor {
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)
        jIRDowncast<JIRInst>(statement)

        return JIRMethodSummaryEdgeProcessor(analysisContext, graph, this, statement)
    }

    override fun isTransparentToFact(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        graph: MethodInstGraph,
        statement: CommonInst,
        fact: FinalFactAp,
    ): Boolean {
        if (apManager !is BaseOnlyApManager) return false
        jIRDowncast<JIRInst>(statement)
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)
        if (graph.isExitPoint(this, statement)) return false

        val callExpr = getCallExpr(statement)
        if (callExpr != null) {
            if (fact.base != AccessPathBase.ClassStatic) return false
            if (analysisContext.taint.hasRulesForCallStatement(statement)) return false
            return classStaticCallIsDefinitelyIrrelevant(
                apManager, analysisContext, callExpr, statement, fact,
            )
        }

        if (statement !is JIRAssignInst && statement !is JIRReturnInst && statement !is JIRThrowInst) {
            return true
        }

        if (statement !is JIRAssignInst) return false
        if (fact.base == AccessPathBase.ClassStatic) {
            return !statement.accept(StaticFieldAccessDetector)
        }
        return !statement.accept(FactBaseAccessDetector(fact.base))
    }

    private fun classStaticCallIsDefinitelyIrrelevant(
        apManager: ApManager,
        context: JIRMethodAnalysisContext,
        call: JIRCallExpr,
        statement: JIRInst,
        fact: FinalFactAp,
    ): Boolean {
        context.cachedRawCallResolution(statement.location.index) {
            context.callResolver.resolve(call, statement, context)
        }.forEach { result ->
            when (result) {
                is JIRCallResolver.MethodResolutionResult.ConcreteMethod -> {
                    if (factIsRelevantToResolvedMethod(apManager, context, result.method, fact)) {
                        return false
                    }
                }

                JIRCallResolver.MethodResolutionResult.MethodResolutionFailed -> Unit
                is JIRCallResolver.MethodResolutionResult.Lambda -> {
                    val tracker = context.lambdaCallResolution[statement.location.index] ?: return@forEach
                    var relevantLambdaSeen = false
                    tracker.forEachRegisteredLambda(object : JIRLambdaTracker.LambdaSubscriber {
                        override fun newLambda(
                            method: JIRMethod,
                            lambdaClass: LambdaAnonymousClassFeature.JIRLambdaClass,
                        ) {
                            val implementation = lambdaClass.findMethodOrNull(method.name, method.description)
                                ?: return
                            val lambda = MethodWithContext(implementation, EmptyMethodContext)
                            if (factIsRelevantToResolvedMethod(apManager, context, lambda, fact)) {
                                relevantLambdaSeen = true
                            }
                        }
                    })
                    if (relevantLambdaSeen) return false
                }
            }
        }
        return true
    }

    override fun factIsRelevantToResolvedMethod(
        apManager: ApManager,
        callerContext: MethodAnalysisContext,
        method: MethodWithContext,
        fact: FactAp,
    ): Boolean {
        if (currentPhase !is Phase.ShallowScan) return true
        if (apManager !is BaseOnlyApManager) return true
        if (fact !is BaseOnlyFinalFactAp && fact !is BaseOnlyInitialFactAp) return true
        if (fact.base != AccessPathBase.ClassStatic) return true
        callerContext as JIRMethodAnalysisContext

        val footprint = classStaticFootprintIndex ?: synchronized(this) {
            classStaticFootprintIndex ?: JIRClassStaticFootprintIndex(
                callerContext.callResolver,
                phaseTaintConfig,
                contexts::toList,
            ).also { classStaticFootprintIndex = it }
        }
        return footprint.mayObserve(method, fact)
    }

    internal enum class ResolvedCallFactRelevance {
        AllRelevant,
        AllSkipped,
        Mixed,
    }

    internal fun resolvedCallFactRelevance(
        apManager: ApManager,
        context: JIRMethodAnalysisContext,
        call: JIRCallExpr,
        statement: JIRInst,
        fact: FactAp,
    ): ResolvedCallFactRelevance {
        if (currentPhase !is Phase.ShallowScan || apManager !is BaseOnlyApManager) {
            return ResolvedCallFactRelevance.AllRelevant
        }
        if (fact.base != AccessPathBase.ClassStatic) return ResolvedCallFactRelevance.AllRelevant

        var hasRelevantTarget = false
        var hasSkippedTarget = false

        fun classify(method: MethodWithContext) {
            if (factIsRelevantToResolvedMethod(apManager, context, method, fact)) {
                hasRelevantTarget = true
            } else {
                hasSkippedTarget = true
            }
        }

        context.callResolver.resolve(call, statement, context).forEach { result ->
            when (result) {
                is JIRCallResolver.MethodResolutionResult.ConcreteMethod -> classify(result.method)
                JIRCallResolver.MethodResolutionResult.MethodResolutionFailed -> Unit
                is JIRCallResolver.MethodResolutionResult.Lambda -> {
                    context.lambdaCallResolution[statement.location.index]?.forEachRegisteredLambda(
                        object : JIRLambdaTracker.LambdaSubscriber {
                            override fun newLambda(
                                method: JIRMethod,
                                lambdaClass: LambdaAnonymousClassFeature.JIRLambdaClass,
                            ) {
                                val implementation = lambdaClass.findMethodOrNull(method.name, method.description)
                                    ?: return
                                classify(MethodWithContext(implementation, EmptyMethodContext))
                            }
                        }
                    )
                }
            }
        }

        return when {
            hasRelevantTarget && hasSkippedTarget -> ResolvedCallFactRelevance.Mixed
            hasSkippedTarget -> ResolvedCallFactRelevance.AllSkipped
            else -> ResolvedCallFactRelevance.AllRelevant
        }
    }

    override fun isReachable(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        base: AccessPathBase,
        statement: CommonInst
    ): Boolean {
        jIRDowncast<JIRMethodAnalysisContext>(analysisContext)
        return analysisContext.localVariableReachability.isReachable(base, statement)
    }

    override fun isValidMethodExitFact(
        apManager: ApManager,
        analysisContext: MethodAnalysisContext,
        fact: FinalFactAp
    ): Boolean {
        return JIRMethodCallFactMapper.isValidMethodExitFact(fact)
    }

    override val methodContextSerializer = JIRMethodContextSerializer(cp)

    override fun onInstructionReached(inst: CommonInst) {

    }

    override fun reportLanguageSpecificRunnerProgress(logger: KLogger) {
        logger.debug {
            val localTotal = factTypeChecker.localFactsTotal.sum()
            val localRejected = factTypeChecker.localFactsRejected.sum()
            val accessTotal = factTypeChecker.accessTotal.sum()
            val accessRejected = factTypeChecker.accessRejected.sum()
            val compatTotal = factTypeChecker.compatibilityTotal.sum()
            val compatRejected = factTypeChecker.compatibilityRejected.sum()
            buildString {
                append("Fact types: ")
                append("local $localRejected/$localTotal (${percentToString(localRejected, localTotal)})")
                append(" | ")
                append("access $accessRejected/$accessTotal (${percentToString(accessRejected, accessTotal)})")
                append(" | ")
                append("compatibility $compatRejected/$compatTotal (${percentToString(compatRejected, compatTotal)})")
            }
        }
    }

    private fun percentToString(current: Long, total: Long): String {
        val percentValue = current.toDouble() / total
        return String.format("%.2f", percentValue * 100) + "%"
    }
}
