package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.python.Position
import org.opentaint.dataflow.configuration.python.TaintCleanAction
import org.opentaint.dataflow.configuration.python.TaintConfigurationItem
import org.opentaint.dataflow.configuration.python.TaintMark
import org.opentaint.dataflow.configuration.python.serialized.PIRUserDefinedRuleInfo
import org.opentaint.dataflow.python.PIRCallAnyArgumentResolver
import org.opentaint.dataflow.python.PIRCallAtomEvaluator
import org.opentaint.dataflow.python.PIRConditionRewriter
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.taint.EvaluatedCleanAction
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintCleanActionEvaluator
import org.opentaint.dataflow.taint.applyCleanerActions
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction

/**
 * Strong-updates the marks a user-defined (semgrep-converted) source/cleaner rule controls when a
 * callee's summary fact is mapped back to the caller: the rule's [PIRUserDefinedRuleInfo.relevantTaintMarks]
 * are removed from the rule's positions so the rule's own action — not a stale propagated mark — decides
 * them. Python mirror of [org.opentaint.dataflow.go.analysis.GoCallRuleBasedSummaryRewriter].
 *
 * Positions resolve in the callee exit frame (`Result` → `AccessPathBase.Return`), the frame the summary
 * fact lives in before [PIRMethodCallSummaryHandler.mapMethodExitToReturnFlowFact].
 */
class PIRCallRuleBasedSummaryRewriter(
    private val callInst: PIRCall,
    private val ctx: PIRMethodAnalysisContext,
    private val apManager: ApManager,
    private val resolvedMethods: Set<PIRFunction>,
) {
    private val config get() = ctx.taint.taintConfig

    private data class UserRuleDefinedAction(
        val rule: TaintConfigurationItem,
        val positions: Set<Position>,
        val controlledMarks: Set<String>,
    )

    private val userRuleDefinedActions: List<UserRuleDefinedAction> by lazy {
        val conditionRewriter = PIRConditionRewriter(
            PIRCallAnyArgumentResolver(callInst), PIRCallAtomEvaluator(callInst)
        )

        val result = mutableListOf<UserRuleDefinedAction>()
        for (sourceRule in resolvedMethods.flatMap { config.sourcesForMethod(it) }) {
            val ruleInfo = sourceRule.info as? PIRUserDefinedRuleInfo ?: continue

            val simplifiedCondition = conditionRewriter.rewrite(sourceRule.condition)
            if (simplifiedCondition.isFalse) continue

            val positions = sourceRule.taint.mapTo(hashSetOf()) { it.pos }
            result += UserRuleDefinedAction(sourceRule, positions, ruleInfo.relevantTaintMarks)
        }

        for (cleanRule in resolvedMethods.flatMap { config.cleanersForMethod(it) }) {
            val ruleInfo = cleanRule.info as? PIRUserDefinedRuleInfo ?: continue

            val simplifiedCondition = conditionRewriter.rewrite(cleanRule.condition)
            if (simplifiedCondition.isFalse) continue

            val positions = cleanRule.cleans.mapTo(hashSetOf()) { it.pos }
            result += UserRuleDefinedAction(cleanRule, positions, ruleInfo.relevantTaintMarks)
        }

        result
    }

    fun rewriteSummaryFact(fact: FinalFactAp): List<Pair<FinalFactAp, FinalFactReader>> {
        val startFactReader = FinalFactReader(fact, apManager)

        val cleanEvaluator = TaintCleanActionEvaluator()

        val cleanedFact = userRuleDefinedActions.applyCleanerActions(
            evalAction = { f, rule, action ->
                val pos = action.pos.resolveAp() ?: return@applyCleanerActions listOf(f)

                cleanEvaluator.removeFinalFact(f, pos, TaintMarkAccessor(action.mark.name), rule, action)
            },
            itemRule = { it.rule },
            itemActions = { action ->
                action.controlledMarks.flatMap { mark ->
                    action.positions.map { TaintCleanAction(TaintMark(mark), it) }
                }
            },
            initial = EvaluatedCleanAction.initial(startFactReader),
        )

        return cleanedFact.mapNotNull {
            val resultFact = it.fact ?: return@mapNotNull null
            resultFact.factAp to resultFact
        }
    }
}
