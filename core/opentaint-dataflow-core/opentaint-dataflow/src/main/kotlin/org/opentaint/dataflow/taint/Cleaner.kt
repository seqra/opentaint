package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.TaintCleanReach

/** A cleaner expressed in the same position language as sources and sinks. */
sealed interface Cleaner {
    val position: PositionAccess

    data class AllMarks(
        override val position: PositionAccess,
    ) : Cleaner

    data class Mark(
        override val position: PositionAccess,
        val mark: TaintMarkAccessor,
        val reach: TaintCleanReach = TaintCleanReach.Exact,
    ) : Cleaner
}

internal val Cleaner.requiresDemandResolution: Boolean
    get() = this is Cleaner.AllMarks || !position.hasAnyField()

internal fun Cleaner.removePrefix(prefix: Accessor): Cleaner {
    val remainingPosition = position.removePrefix(prefix)
    return when (this) {
        is Cleaner.AllMarks -> copy(position = remainingPosition)
        is Cleaner.Mark -> copy(position = remainingPosition)
    }
}

class TaintCleanActionEvaluator {
    fun removeAllFacts(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ): List<EvaluatedCleanAction> {
        val fact = evc.fact ?: return listOf(evc)
        if (from.base() != fact.factAp.base) return listOf(evc)
        val cleaned = fact.clean(Cleaner.AllMarks(from)) ?: return listOf(evc)
        return clean(cleaned, fact, rule, action, evc)
    }

    fun removeFinalFact(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        markRestriction: TaintMarkAccessor,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        reach: TaintCleanReach = TaintCleanReach.Exact,
    ): List<EvaluatedCleanAction> {
        val fact = evc.fact ?: return listOf(evc)
        if (from.base() != fact.factAp.base) return listOf(evc)
        val cleaned = fact.clean(Cleaner.Mark(from, markRestriction, reach)) ?: return listOf(evc)
        return clean(cleaned, fact, rule, action, evc)
    }

    private fun clean(
        cleaned: FinalFactAp.CleanResult,
        fact: FinalFactReader,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        evc: EvaluatedCleanAction
    ): List<EvaluatedCleanAction> {
        val result = mutableListOf<EvaluatedCleanAction>()
        if (cleaned.removedAlternative) {
            val actionInfo = EvaluatedCleanAction.ActionInfo(rule, action)
            result += EvaluatedCleanAction(null, actionInfo, evc)
        }

        return cleaned.survivingFacts.mapTo(result) { cleanedFact ->
            val resultFact = fact.replaceFact(cleanedFact)
            val actionInfo = EvaluatedCleanAction.ActionInfo(rule, action)
            EvaluatedCleanAction(resultFact, actionInfo, evc)
        }
    }
}

inline fun <T, A> List<T>.applyCleanerActions(
    evalAction: (EvaluatedCleanAction, CommonTaintConfigurationItem, A) -> List<EvaluatedCleanAction>,
    itemRule: (T) -> CommonTaintConfigurationItem,
    itemActions: (T) -> List<A>,
    initial: EvaluatedCleanAction
): List<EvaluatedCleanAction> {
    val resultFacts = mutableListOf<EvaluatedCleanAction>()
    var unprocessedFacts = listOf(initial)
    for (item in this) {
        if (unprocessedFacts.isEmpty()) continue

        val rule = itemRule(item)
        val actions = itemActions(item)
        for (action in actions) {
            if (unprocessedFacts.isEmpty()) continue

            unprocessedFacts = unprocessedFacts.evaluatedCleanAction(evalAction, rule, action, resultFacts)
        }
    }

    resultFacts.addAll(unprocessedFacts)
    return resultFacts
}

inline fun <A> List<EvaluatedCleanAction>.evaluatedCleanAction(
    evalAction: (EvaluatedCleanAction, CommonTaintConfigurationItem, A) -> List<EvaluatedCleanAction>,
    rule: CommonTaintConfigurationItem,
    action: A,
    resultFacts: MutableList<EvaluatedCleanAction>
): List<EvaluatedCleanAction> {
    val nextIterationFacts = mutableListOf<EvaluatedCleanAction>()

    for (fact in this) {
        val updatedFacts = evalAction(fact, rule, action)

        for (updatedFact in updatedFacts) {
            if (updatedFact.fact == null) {
                resultFacts.add(updatedFact)
                continue
            }
            nextIterationFacts.add(updatedFact)
        }
    }
    return nextIterationFacts
}
