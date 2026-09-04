package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.Action
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.CopyMark
import org.opentaint.dataflow.configuration.jvm.RemoveAllMarks
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintCleanActionEvaluator
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.EvaluatedCleanAction
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PassActionEvaluator
import org.opentaint.dataflow.taint.SourceActionEvaluator
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.dataflow.taint.applyCleanerActions
import org.opentaint.util.Maybe
import org.opentaint.util.maybeFlatMap
import org.opentaint.util.onSome

object TaintConfigUtils {
    fun <T> applyEntryPointConfig(
        rules: List<RuleWithCondition<TaintEntryPointSource>>,
        taintActionEvaluator: SourceActionEvaluator<T>,
        onActionApplied: (TaintEntryPointSource, AssignMark) -> Unit = { _, _ -> },
    ) = applyAssignMark<TaintEntryPointSource, T>(
        rules, taintActionEvaluator,
        TaintEntryPointSource::actionsAfter,
        onActionApplied,
    )

    private inline fun <reified T : TaintConfigurationItem, R> applyAssignMark(
        rules: List<RuleWithCondition<T>>,
        taintActionEvaluator: SourceActionEvaluator<R>,
        actionsAfter: (T) -> List<Action>,
        crossinline onActionApplied: (T, AssignMark) -> Unit,
    ): Maybe<List<R>> = rules
        .applicableRules(conditionEvaluator = null)
        .maybeFlatMap { item ->
            actionsAfter(item)
                .filterIsInstance<AssignMark>()
                .maybeFlatMap { action ->
                    taintActionEvaluator.accept(item, action).onSome { results ->
                        if (results.isNotEmpty()) onActionApplied(item, action)
                    }
                }
        }

    fun <T> applyPassThrough(
        rules: List<RuleWithCondition<TaintPassThrough>>,
        conditionEvaluator: TaintFactAwareConditionEvaluator,
        taintActionEvaluator: PassActionEvaluator<T>
    ): Maybe<List<T>> {
        val rules = rules.applicableRules(conditionEvaluator)
        return rules
            .maybeFlatMap { item ->
                item.actionsAfter.maybeFlatMap {
                    taintActionEvaluator.accept(item, it)
                }
            }
    }

    fun applyCleaner(
        rules: List<RuleWithCondition<TaintCleaner>>,
        initialFact: FinalFactReader,
        conditionEvaluator: TaintFactAwareConditionEvaluator,
        taintActionEvaluator: JIRTaintCleanActionEvaluator
    ): List<EvaluatedCleanAction> {
        val rules = rules.applicableRules(conditionEvaluator)
        return rules.applyCleanerActions(
            evaluator = taintActionEvaluator,
            itemRule = { it },
            itemActions = { it.actionsAfter },
            initial = EvaluatedCleanAction.initial(initialFact)
        )
    }

    private fun <T> List<RuleWithCondition<T>>.applicableRules(
        conditionEvaluator: TaintFactAwareConditionEvaluator?
    ): List<T> {
        val applicableRules = filter {
            val simplifiedCondition = it.condition
            val conditionExpr = when {
                simplifiedCondition.isFalse -> return@filter false
                simplifiedCondition.isTrue -> return@filter true
                else -> simplifiedCondition.expr
            }

            conditionEvaluator?.evalWithAssumptionsCheck(conditionExpr) ?: false
        }

        return applicableRules.map { it.rule }
    }

    inline fun <T> Iterable<T>.applyCleanerActions(
        initial: EvaluatedCleanAction,
        body: (T, EvaluatedCleanAction) -> List<EvaluatedCleanAction>
    ): List<EvaluatedCleanAction> {
        var unprocessedFacts = listOf(initial)
        for (action in this) {
            val next = mutableListOf<EvaluatedCleanAction>()
            for (f in unprocessedFacts) {
                next += body(action, f)
            }
            unprocessedFacts = next
        }
        return unprocessedFacts
    }

    inline fun <T> List<T>.applyCleanerActions(
        evaluator: JIRTaintCleanActionEvaluator,
        itemRule: (T) -> TaintConfigurationItem,
        itemActions: (T) -> List<Action>,
        initial: EvaluatedCleanAction
    ): List<EvaluatedCleanAction> = applyCleanerActions(
        { fact, rule, action ->
            evaluator.accept(fact, rule, action)
        },
        itemRule, itemActions, initial
    )

    fun JIRTaintCleanActionEvaluator.accept(
        fact: EvaluatedCleanAction,
        rule: CommonTaintConfigurationItem,
        action: Action
    ) = when (action) {
        is RemoveMark -> evaluate(fact, rule, action)
        is RemoveAllMarks -> evaluate(fact, rule, action)
        else -> listOf(fact)
    }

    fun <T> PassActionEvaluator<T>.accept(rule: CommonTaintConfigurationItem, action: Action): Maybe<List<T>> =
        when (val it = action) {
            is CopyMark -> propagateTaint(rule, it, it.from.resolveAp(), it.to.resolveAp(), TaintMarkAccessor(it.mark.name))
            is CopyAllMarks -> propagateData(rule, it, it.from.resolveAp(), it.to.resolveAp())
            else -> Maybe.none()
        }

    fun <T> SourceActionEvaluator<T>.accept(rule: CommonTaintConfigurationItem, action: AssignMark): Maybe<List<T>> =
        evaluate(rule, action, action.position.resolveAp(), TaintMarkAccessor(action.mark.name))
}
