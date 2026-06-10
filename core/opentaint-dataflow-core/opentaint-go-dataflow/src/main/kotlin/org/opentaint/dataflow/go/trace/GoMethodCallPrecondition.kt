package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.CallPreconditionFact.CallFailurePreconditionFact
import org.opentaint.dataflow.ap.ifds.trace.MethodCallPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.go.GoMethodCallFactMapper.factIsRelevantToMethodCall
import org.opentaint.dataflow.go.GoMethodCallFactMapper.mapMethodCallToStartFlowAnyFact
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.dataflow.go.analysis.forEachAliasAtStatement
import org.opentaint.dataflow.go.analysis.forEachPossibleAliasAtStatement
import org.opentaint.dataflow.go.analysis.resolvePosAccess
import org.opentaint.dataflow.go.rules.GoRuleConditionRewriter
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.go.rules.accept
import org.opentaint.dataflow.go.signature
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.TaintPassActionPreconditionEvaluator
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.dataflow.taint.evaluatePassRulePrecondition
import org.opentaint.dataflow.taint.evaluateSourceRulePrecondition
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

class GoMethodCallPrecondition(
    override val apManager: ApManager,
    private val callExpr: GoCallExpr,
    private val statement: GoIRInst,
    private val analysisContext: GoMethodAnalysisContext,
) : MethodCallPrecondition.Default {
    private val rulesProvider: GoTaintRulesProvider
        get() = analysisContext.taint.taintConfig

    private val returnValue: GoIRValue?
        get() = GoFlowFunctionUtils.extractResultRegister(statement)

    private val callSignature: GoFunctionSignature?
        get() = callExpr.signature()

    override fun mapExit2Return(fact: InitialFactAp): List<InitialFactAp> =
        GoMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, fact)

    override fun factPrecondition(fact: InitialFactAp): List<CallPrecondition> {
        val result = mutableListOf<CallPrecondition>()

        result += preconditionForFact(fact)?.let { PreconditionFactsForInitialFact(fact, it) }
            ?: CallPrecondition.Unchanged

        analysisContext.aliasAnalysis.forEachPossibleAliasAtStatement(statement, fact) { aliasedFact ->
            preconditionForFact(aliasedFact)?.let {
                result += PreconditionFactsForInitialFact(aliasedFact, it)
            }
        }

        // todo: do we need to explore all accessors?
        analysisContext.aliasAnalysis.forEachAliasAtStatement(statement, fact) { aliasedFact ->
            preconditionForFact(aliasedFact)?.let {
                result += PreconditionFactsForInitialFact(aliasedFact, it)
            }
        }

        return result
    }

    override fun factPreconditionResolutionFailure(
        fact: InitialFactAp,
        startFactBase: AccessPathBase
    ): List<CallFailurePreconditionFact> {
        val result = mutableListOf<CallFailurePreconditionFact>()

        if (startFactBase != AccessPathBase.Return) {
            result += CallPreconditionFact.UnresolvedCallSkip
        }

        factPassRulePrecondition(fact, startFactBase).mapTo(result) {
            CallPreconditionFact.CallToReturnTaintRule(it)
        }

        return result
    }

    private fun preconditionForFact(fact: InitialFactAp): List<CallPreconditionFact>? {
        if (!factIsRelevantToMethodCall(statement, returnValue, callExpr, fact)) return null

        val preconditions = mutableListOf<CallPreconditionFact>()

        val ret = returnValue
        if (ret != null) {
            val returnValueBase = GoFlowFunctionUtils.accessPathBase(ret, callExpr.enclosingMethod)
            if (returnValueBase == fact.base) {
                preconditions.preconditionForFact(fact, AccessPathBase.Return)
            }
        }

        mapMethodCallToStartFlowAnyFact(
            statement, callExpr, factAp = fact
        ) { callerFact, startBase ->
            preconditions.preconditionForFact(callerFact, startBase)
        }

        return preconditions
    }

    private fun MutableList<CallPreconditionFact>.preconditionForFact(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ) {
        factSourceRulePrecondition(fact, startBase).mapTo(this) {
            CallPreconditionFact.CallToReturnTaintRule(it)
        }

        this += CallPreconditionFact.CallToStart(fact, startBase)
    }

    private fun factSourceRulePrecondition(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ): List<TaintRulePrecondition> {
        val signature = callSignature ?: return emptyList()
        val sourceRules = rulesProvider.sourceRulesForCall(signature)
        if (sourceRules.isEmpty()) return emptyList()

        val entryFactReader = InitialFactReader(fact.rebase(startBase), apManager)
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(entryFactReader)

        val result = mutableListOf<TaintRulePrecondition>()

        for (rule in sourceRules) {
            result += evaluateSourceRulePrecondition(
                rule,
                rule.actionsAfter,
                ruleCondition = { condition },
                sourcePreconditionEvaluator = sourcePreconditionEvaluator,
                evalAction = { r, a -> evaluate(r, a, a.resolvePosAccess(), TaintMarkAccessor(a.mark)) },
                conditionRewriter = GoRuleConditionRewriter(callExpr, statement, returnValue),
            )
        }

        return result
    }

    private fun factPassRulePrecondition(
        fact: InitialFactAp,
        startFactBase: AccessPathBase,
    ): List<TaintRulePrecondition> {
        val signature = callSignature ?: return emptyList()
        val passRules = rulesProvider.passThroughRulesForCall(signature)
        if (passRules.isEmpty()) return emptyList()

        val entryFactReader = InitialFactReader(fact.rebase(startFactBase), apManager)
        val rulePreconditionEvaluator = TaintPassActionPreconditionEvaluator(entryFactReader)

        val result = mutableListOf<TaintRulePrecondition>()

        for (rule in passRules) {
            result += evaluatePassRulePrecondition(
                rule,
                rule.actionsAfter,
                { mkTrue() },
                rulePreconditionEvaluator,
                evalAction = { r, a -> accept(r, a) },
                RuleConditionRewriter.Unconditional,
                { mapExit2Return(it) }
            )
        }

        return result
    }

    override fun allStatements(): List<CommonInst> =
        statement.location.functionBody.instructions
}
