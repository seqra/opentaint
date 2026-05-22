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
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition.PassRuleCondition
import org.opentaint.dataflow.configuration.CommonTaintAssignAction
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoMethodCallFactMapper
import org.opentaint.dataflow.go.GoMethodCallFactMapper.factIsRelevantToMethodCall
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.dataflow.go.rules.TaintRules
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintPassActionPreconditionEvaluator
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue
import org.opentaint.util.onSome

/**
 * Call-site precondition for Go. For each fact observed after a call statement,
 * returns the set of preconditions (call-to-return source/pass rule applications and
 * call-to-start mappings) under which the corresponding flow function would have
 * produced that fact.
 *
 * Mirrors the JIR implementation in spirit; simplified for the Go MVP rule model
 * (no condition expressions, no aliasing).
 */
class GoMethodCallPrecondition(
    private val apManager: ApManager,
    private val returnValueFromFramework: GoIRValue?,
    private val callExpr: GoCallExpr,
    private val statement: GoIRInst,
    private val analysisContext: GoMethodAnalysisContext,
) : MethodCallPrecondition {
    private val rulesProvider: GoTaintRulesProvider
        get() = analysisContext.taint.taintConfig

    private val returnValue: GoIRValue?
        get() = returnValueFromFramework ?: GoFlowFunctionUtils.extractResultRegister(statement)

    private val calleeName: String? get() = callExpr.calleeName

    /** Dummy assign-action used to identify a source rule in a [TaintRulePrecondition.Source]. */
    private data class GoSourceAction(val rule: TaintRules.Source) : CommonTaintAssignAction

    /** Pass rule condition: the single precondition fact (in caller namespace). */
    private data class GoPassRuleCondition(val fact: InitialFactAp) : PassRuleCondition

    override fun factPrecondition(fact: InitialFactAp): List<CallPrecondition> {
        val preconditionFacts = preconditionForFact(fact)
            ?: return listOf(CallPrecondition.Unchanged)

        if (preconditionFacts.isEmpty()) {
            return listOf(CallPrecondition.Unchanged)
        }

        return listOf(PreconditionFactsForInitialFact(fact, preconditionFacts))
    }

    private fun preconditionForFact(fact: InitialFactAp): List<CallPreconditionFact>? {
        if (!factIsRelevantToMethodCall(statement, returnValue, callExpr, fact)) {
            return null
        }

        val preconditions = mutableListOf<CallPreconditionFact>()

        // Return value mapping: caller-local register that holds the call result → callee Return base.
        val ret = returnValue
        if (ret != null) {
            val returnValueBase = GoFlowFunctionUtils.accessPathBase(ret, callExpr.enclosingMethod)
            if (returnValueBase != null && returnValueBase == fact.base) {
                preconditions.preconditionForFact(fact, AccessPathBase.Return)
            }
        }

        // Caller args/receiver/closure bindings → callee Argument bases.
        GoMethodCallFactMapper.mapMethodCallToStartFlowAnyFact(
            statement, callExpr, returnValue = null, factAp = fact
        ) { callerFact, startBase ->
            preconditions.preconditionForFact(callerFact, startBase)
        }

        return preconditions
    }

    private fun MutableList<CallPreconditionFact>.preconditionForFact(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ) {
        // Source rule applications that could produce this fact at the call site.
        factSourceRulePrecondition(fact, startBase).mapTo(this) {
            CallPreconditionFact.CallToReturnTaintRule(it)
        }

        // The fact may have entered through the callee normally.
        this += CallPreconditionFact.CallToStart(fact, startBase)
    }

    private fun factSourceRulePrecondition(
        fact: InitialFactAp,
        startBase: AccessPathBase,
    ): List<TaintRulePrecondition.Source> {
        val name = calleeName ?: return emptyList()
        val sourceRules = rulesProvider.sourceRulesForCall(name)
        if (sourceRules.isEmpty()) return emptyList()

        val result = mutableListOf<TaintRulePrecondition.Source>()
        for (rule in sourceRules) {
            val rulePosBase = GoFlowFunctionUtils.resolvePosition(rule.pos)
            if (rulePosBase != startBase) continue
            if (!fact.startsWithAccessor(TaintMarkAccessor(rule.mark))) continue

            result += TaintRulePrecondition.Source(rule, setOf(GoSourceAction(rule)))
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

    private fun factPassRulePrecondition(
        fact: InitialFactAp,
        startFactBase: AccessPathBase,
    ): List<TaintRulePrecondition.Pass> {
        val name = calleeName ?: return emptyList()
        val passRules = rulesProvider.passRulesForCall(name)
        if (passRules.isEmpty()) return emptyList()

        val result = mutableListOf<TaintRulePrecondition.Pass>()
        val entryFactReader = InitialFactReader(fact.rebase(startFactBase), apManager)
        val rulePreconditionEvaluator = TaintPassActionPreconditionEvaluator(entryFactReader)

        for (rule in passRules) {
            val from = GoFlowFunctionUtils.resolvePositionAccess(rule.from)
            val to = GoFlowFunctionUtils.resolvePositionAccess(rule.to)

            rulePreconditionEvaluator.propagateData(rule, rule, from, to).onSome { facts ->
                facts.forEach { calleeFact ->
                    val callerFacts = GoMethodCallFactMapper.mapMethodExitToReturnFlowFact(statement, calleeFact.second)
                    for (callerFact in callerFacts) {
                        result += TaintRulePrecondition.Pass(
                            rule,
                            setOf(calleeFact.first),
                            GoPassRuleCondition(callerFact),
                        )
                    }
                }
            }
        }
        return result
    }

    override fun resolvePassRuleCondition(
        precondition: PassRuleCondition
    ): List<MethodCallPrecondition.PassRuleConditionFacts> {
        precondition as GoPassRuleCondition
        return listOf(MethodCallPrecondition.PassRuleConditionFacts(listOf(precondition.fact)))
    }
}
