package org.opentaint.dataflow.jvm.ap.ifds.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.ReadableAccessorList
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact.CallFailurePreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper.factIsRelevantToMethodCall
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.evaluateSourceRule
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.forEachPossibleAliasAtStatement
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.FactReader
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.dataflow.taint.TaintPassActionPreconditionEvaluator
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.dataflow.taint.evaluatePassRulePrecondition
import org.opentaint.dataflow.taint.passRulePrecondition
import org.opentaint.ir.api.common.cfg.CommonInst
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

    private val taintCtx get() = analysisContext.taint

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
        evaluateSourceRules(
            InitialFactReader(fact.rebase(startBase), apManager),
            mkSource = { r, a -> this += TaintRulePrecondition.Source(r, a) },
            mkPass = { r, a, e -> this += TaintRulePrecondition.Pass(r, a, PassRuleCondition.Expr(e)) },
        )
    }

    private fun MutableList<TaintRulePrecondition>.factPassRulePrecondition(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ) {
        val entryFactReader = InitialFactReader(fact.rebase(startBase), apManager)
        evaluatePassRules(TaintPassActionPreconditionEvaluator(entryFactReader), ::mapExit2Return) { r, a, f, e ->
            this += passRulePrecondition(r, a, f, e)
        }
    }

    fun evaluateSourceRules(
        factReader: FactReader,
        mkSource: (TaintMethodSource, Set<CommonTaintAssignAction>) -> Unit,
        mkPass: (TaintMethodSource, Set<CommonTaintAssignAction>, TaintMarkAwareConditionExpr) -> Unit,
    ) {
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(factReader)

        for (rule in taintCtx.sourceRulesForCallStatement(statement, callExpr, returnValue, fact = null)) {
            sourcePreconditionEvaluator.evaluateSourceRule(rule, mkSource, mkPass)
        }
    }

    fun <F> evaluatePassRules(
        rulePreconditionEvaluator: TaintPassActionPreconditionEvaluator<F>,
        mapExit2Return: (F) -> List<F>,
        mkPass: (TaintPassThrough, CommonTaintAction, F, TaintMarkAwareConditionExpr?) -> Unit,
    ) where F : FactAp, F : ReadableAccessorList<F> {
        val passRules = taintCtx.passRulesForCallStatement(statement, callExpr, returnValue, fact = null).toMutableList()

        analysisContext.analysisManager.params.defaultGetModel?.run {
            passRules += defaultPropagationRules(callExpr.method.method)
        }

        for (rule in passRules) {
            evaluatePassRulePrecondition(
                rule,
                rule.rule.actionsAfter,
                rulePreconditionEvaluator,
                evalAction = { r, a -> accept(r, a) },
                mapExit2Return,
                mkPass,
            )
        }
    }

    override fun allStatements(): List<CommonInst> =
        statement.location.method.instList.toList()

    override fun mapExit2Return(fact: InitialFactAp): List<InitialFactAp> =
        methodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact)
}
