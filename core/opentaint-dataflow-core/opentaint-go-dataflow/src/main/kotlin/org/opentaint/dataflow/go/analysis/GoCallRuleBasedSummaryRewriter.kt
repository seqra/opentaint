package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.go.serialized.GoUserDefinedRuleInfo
import org.opentaint.dataflow.go.GoCallExpr
import org.opentaint.dataflow.go.GoFlowFunctionUtils.resolvePosAccess
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.signature
import org.opentaint.dataflow.go.rules.GoRuleConditionRewriter
import org.opentaint.dataflow.go.rules.Position
import org.opentaint.dataflow.go.rules.RemoveMark
import org.opentaint.dataflow.go.rules.TaintRule
import org.opentaint.dataflow.taint.EvaluatedCleanAction
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintCleanActionEvaluator
import org.opentaint.dataflow.taint.applyCleanerActions
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.value.GoIRValue

class GoCallRuleBasedSummaryRewriter(
    private val statement: GoIRInst,
    private val callExpr: GoCallExpr,
    private val returnValue: GoIRValue?,
    private val analysisContext: GoMethodAnalysisContext,
    private val apManager: ApManager,
) {
    private val config get() = analysisContext.taint.taintConfig

    private val callSignature: GoFunctionSignature?
        get() = callExpr.signature()

    private data class UserRuleDefinedAction(
        val rule: TaintRule,
        val positions: Set<Position>,
        val controlledMarks: Set<String>
    )

    private val userRuleDefinedActions: List<UserRuleDefinedAction> by lazy {
        val signature = callSignature ?: return@lazy emptyList()

        val conditionRewriter = GoRuleConditionRewriter(callExpr, statement, returnValue)

        val result = mutableListOf<UserRuleDefinedAction>()
        for (sourceRule in config.sourceRulesForCall(signature, allRelevant = true)) {
            val ruleInfo = sourceRule.info as? GoUserDefinedRuleInfo ?: continue

            val simplifiedCondition = conditionRewriter.rewrite(sourceRule.condition)
            if (simplifiedCondition.isFalse) continue

            val positions = sourceRule.actionsAfter.mapTo(hashSetOf()) { it.rawPosition() }
            result += UserRuleDefinedAction(sourceRule, positions, ruleInfo.relevantTaintMarks)
        }

        for (cleanRule in config.cleanerRulesForCall(signature, allRelevant = true)) {
            val ruleInfo = cleanRule.info as? GoUserDefinedRuleInfo ?: continue

            val simplifiedCondition = conditionRewriter.rewrite(cleanRule.condition)
            if (simplifiedCondition.isFalse) continue

            val positions = cleanRule.actionsAfter.filterIsInstance<RemoveMark>().mapTo(hashSetOf()) { it.pos }
            result += UserRuleDefinedAction(cleanRule, positions, ruleInfo.relevantTaintMarks)
        }

        result
    }

    fun rewriteSummaryFact(fact: FinalFactAp): List<Pair<FinalFactAp, FinalFactReader>> {
        val startFactReader = FinalFactReader(fact, apManager)

        val cleanEvaluator = TaintCleanActionEvaluator()

        val cleanedFact = userRuleDefinedActions.applyCleanerActions(
            evalAction = { f, rule, action ->
                val pos = action.pos.resolvePosAccess()
                cleanEvaluator.removeFinalFact(f, pos, TaintMarkAccessor(action.mark), rule, action)
            },
            itemRule = { it.rule },
            itemActions = { action ->
                action.controlledMarks.flatMap { mark ->
                    action.positions.map { RemoveMark(mark, it) }
                }
            },
            initial = EvaluatedCleanAction.initial(startFactReader)
        )

        return cleanedFact.mapNotNull {
            val resultFact = it.fact ?: return@mapNotNull null
            resultFact.factAp to resultFact
        }
    }
}
