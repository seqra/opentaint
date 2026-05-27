package org.opentaint.dataflow.jvm.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact.CallFailurePreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.jvm.ap.ifds.CallPositionToJIRValueResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRMarkAwareConditionRewriter
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper.factIsRelevantToMethodCall
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.forEachPossibleAliasAtStatement
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintPassActionPreconditionEvaluator
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.dataflow.taint.evaluatePassRulePrecondition
import org.opentaint.dataflow.taint.evaluateSourceRulePrecondition
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRMethodCallPrecondition(
    override val apManager: ApManager,
    private val analysisContext: JIRMethodAnalysisContext,
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
    private val statement: JIRInst,
) : MethodCallPrecondition.Default {
    private val methodCallFactMapper: MethodCallFactMapper get() = analysisContext.methodCallFactMapper

    private val jIRValueResolver = CallPositionToJIRValueResolver(callExpr, returnValue)
    private val method = callExpr.callee

    private val taintConfig get() = analysisContext.taint.taintConfig as TaintRulesProvider

    override fun factPrecondition(fact: InitialFactAp): List<CallPrecondition> {
        val results = mutableListOf<CallPrecondition>()

        results += preconditionForFact(fact)?.let { PreconditionFactsForInitialFact(fact, it) }
            ?: CallPrecondition.Unchanged

        analysisContext.aliasAnalysis?.forEachPossibleAliasAtStatement(statement, fact) { aliasedFact ->
            preconditionForFact(aliasedFact)?.let { results += PreconditionFactsForInitialFact(aliasedFact, it) }
        }

        return results
    }

    override fun factPreconditionResolutionFailure(
        fact: InitialFactAp,
        startFactBase: AccessPathBase
    ): List<CallFailurePreconditionFact> {
        val preconditions = mutableListOf<CallFailurePreconditionFact>()

        if (startFactBase != AccessPathBase.Return) {
            preconditions += CallPreconditionFact.UnresolvedCallSkip
        }

        preconditions += rulePreconditionForFactResolutionFailure(fact, startFactBase)

        return preconditions
    }

    private fun preconditionForFact(fact: InitialFactAp): List<CallPreconditionFact>? {
        if (!factIsRelevantToMethodCall(statement, returnValue, callExpr, fact)) {
            return null
        }

        val preconditions = mutableListOf<CallPreconditionFact>()

        if (returnValue != null) {
            val returnValueBase = MethodFlowFunctionUtils.accessPathBase(returnValue)
            if (returnValueBase == fact.base) {
                preconditions.preconditionForFact(fact, AccessPathBase.Return)
            }
        }

        val method = callExpr.callee
        JIRMethodCallFactMapper.mapMethodCallToStartFlowFact(
            statement, method,
            callExpr,
            returnValue = null,
            fact = fact
        ) { callerFact, startFactBase ->
            preconditions.preconditionForFact(callerFact, startFactBase)
        }

        return preconditions
    }

    private fun MutableList<CallPreconditionFact>.preconditionForFact(fact: InitialFactAp, startBase: AccessPathBase) {
        val rulePreconditions = mutableListOf<TaintRulePrecondition>()
        rulePreconditions.factSourceRulePrecondition(fact, startBase)

        rulePreconditions.mapTo(this) { CallPreconditionFact.CallToReturnTaintRule(it) }

        this += CallPreconditionFact.CallToStart(fact, startBase)
    }

    private fun rulePreconditionForFactResolutionFailure(
        fact: InitialFactAp,
        startBase: AccessPathBase
    ): List<CallFailurePreconditionFact> {
        val rulePreconditions = mutableListOf<TaintRulePrecondition>()
        rulePreconditions.factPassRulePrecondition(fact, startBase)

        return rulePreconditions.map { CallPreconditionFact.CallToReturnTaintRule(it) }
    }

    private fun MutableList<TaintRulePrecondition>.factSourceRulePrecondition(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ) {
        val entryFactReader = InitialFactReader(fact.rebase(startBase), apManager)
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(
            entryFactReader
        )

        val conditionRewriter = JIRMarkAwareConditionRewriter(
            jIRValueResolver,
            analysisContext, statement
        )

        for (rule in taintConfig.sourceRulesForMethod(method, statement, fact = null)) {
            evaluateSourceRulePrecondition(rule, sourcePreconditionEvaluator, conditionRewriter)
        }
    }

    private fun MutableList<TaintRulePrecondition>.factPassRulePrecondition(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ) {
        val passRules = taintConfig.passTroughRulesForMethod(method, statement, fact = null).toList()
        if (passRules.isEmpty()) return

        val entryFactReader = InitialFactReader(fact.rebase(startBase), apManager)
        val rulePreconditionEvaluator = TaintPassActionPreconditionEvaluator(entryFactReader)

        val conditionRewriter = JIRMarkAwareConditionRewriter(
            jIRValueResolver,
            analysisContext, statement
        )

        for (rule in passRules) {
            evaluatePassRulePrecondition(rule, rulePreconditionEvaluator, conditionRewriter)
        }
    }

    private fun MutableList<TaintRulePrecondition>.evaluateSourceRulePrecondition(
        rule: TaintMethodSource,
        sourcePreconditionEvaluator: TaintSourceActionPreconditionEvaluator,
        conditionRewriter: JIRMarkAwareConditionRewriter,
    ) {
        this += evaluateSourceRulePrecondition(
            rule,
            rule.actionsAfter,
            ruleCondition = { this.condition },
            sourcePreconditionEvaluator = sourcePreconditionEvaluator,
            evalAction = { r, a -> evaluate(r, a, a.position.resolveAp(), TaintMarkAccessor(a.mark.name)) },
            conditionRewriter = conditionRewriter,
        )
    }

    private fun MutableList<TaintRulePrecondition>.evaluatePassRulePrecondition(
        rule: TaintPassThrough,
        rulePreconditionEvaluator: TaintPassActionPreconditionEvaluator,
        conditionRewriter: JIRMarkAwareConditionRewriter
    ) {
        this += evaluatePassRulePrecondition(
            rule,
            rule.actionsAfter,
            { condition },
            rulePreconditionEvaluator,
            evalAction = { r, a -> accept(r, a) },
            conditionRewriter,
            { mapExit2Return(it) }
        )
    }

    override fun mapExit2Return(fact: InitialFactAp): List<InitialFactAp> =
        methodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact)
}
