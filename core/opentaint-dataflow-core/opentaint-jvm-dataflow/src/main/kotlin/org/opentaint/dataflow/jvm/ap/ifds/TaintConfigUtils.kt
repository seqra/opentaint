package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.Action
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.CopyAllMarks
import org.opentaint.dataflow.configuration.jvm.CopyMark
import org.opentaint.dataflow.configuration.jvm.RemoveAllMarks
import org.opentaint.dataflow.configuration.jvm.RemoveMark
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.jvm.ap.ifds.taint.ConditionEvaluator
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintCleanActionEvaluator
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.EvaluatedCleanAction
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.PassActionEvaluator
import org.opentaint.dataflow.taint.SourceActionEvaluator
import org.opentaint.dataflow.taint.applyCleanerActions
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.util.Maybe
import org.opentaint.util.maybeFlatMap

object TaintConfigUtils {
    fun sinkRules(config: TaintRulesProvider, method: CommonMethod, statement: CommonInst, fact: FactAp?) =
        config.sinkRulesForMethod(method, statement, fact)

    fun <T> applyEntryPointConfig(
        config: TaintRulesProvider,
        method: CommonMethod,
        fact: FactAp?,
        conditionEvaluator: ConditionEvaluator<Boolean>,
        taintActionEvaluator: SourceActionEvaluator<T>
    ) = applyAssignMark<TaintEntryPointSource, T>(
        config.entryPointRulesForMethod(method, fact), conditionEvaluator, taintActionEvaluator,
        TaintEntryPointSource::condition, TaintEntryPointSource::actionsAfter
    )

    private inline fun <reified T : TaintConfigurationItem, R> applyAssignMark(
        rules: Iterable<T>,
        conditionEvaluator: ConditionEvaluator<Boolean>,
        taintActionEvaluator: SourceActionEvaluator<R>,
        condition: (T) -> Condition,
        actionsAfter: (T) -> List<Action>
    ): Maybe<List<R>> = rules
        .filter { conditionEvaluator.eval(condition(it)) }
        .maybeFlatMap { item ->
            actionsAfter(item)
                .filterIsInstance<AssignMark>()
                .maybeFlatMap { taintActionEvaluator.accept(item, it) }
        }

    fun <T> applyPassThrough(
        config: TaintRulesProvider,
        method: CommonMethod,
        statement: CommonInst,
        fact: FactAp?,
        conditionEvaluator: ConditionEvaluator<Boolean>,
        taintActionEvaluator: PassActionEvaluator<T>
    ): Maybe<List<T>> =
        config.passTroughRulesForMethod(method, statement, fact)
            .filter { conditionEvaluator.eval(it.condition) }
            .maybeFlatMap { item ->
                item.actionsAfter.maybeFlatMap {
                    taintActionEvaluator.accept(item, it)
                }
            }

    fun applyCleaner(
        config: TaintRulesProvider,
        method: CommonMethod,
        statement: CommonInst,
        initialFact: FinalFactReader,
        conditionEvaluator: ConditionEvaluator<Boolean>,
        taintActionEvaluator: JIRTaintCleanActionEvaluator
    ): List<EvaluatedCleanAction> {
        val rules = config.cleanerRulesForMethod(method, statement, initialFact.factAp)
            .filter { conditionEvaluator.eval(it.condition) }

        return rules.applyCleanerActions(
            evaluator = taintActionEvaluator,
            itemRule = { it },
            itemActions = { it.actionsAfter },
            initial = EvaluatedCleanAction.initial(initialFact)
        )
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
