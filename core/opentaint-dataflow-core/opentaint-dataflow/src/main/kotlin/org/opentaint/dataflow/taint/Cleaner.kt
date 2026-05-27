package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem

class TaintCleanActionEvaluator {
    fun removeAllFacts(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ): List<EvaluatedCleanAction> {
        val fact = evc.fact ?: return listOf(evc)

        if (!fact.containsPosition(from)) return listOf(evc)

        if (from is PositionAccess.Simple) {
            val actionInfo = EvaluatedCleanAction.ActionInfo(rule, action)
            return listOf(EvaluatedCleanAction(fact = null, actionInfo, evc))
        }

        val cleanAccessors = from.accessorList()
        return cleanAccessors(cleanAccessors, fact, rule, action, evc)
    }

    fun removeFinalFact(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        markRestriction: TaintMarkAccessor,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ): List<EvaluatedCleanAction> {
        val fact = evc.fact ?: return listOf(evc)

        if (!fact.containsPositionWithTaintMark(from, markRestriction)) return listOf(evc)

        val cleanAccessors = from.accessorList() + markRestriction
        return cleanAccessors(cleanAccessors, fact, rule, action, evc)
    }

    private fun cleanAccessors(
        accessors: List<Accessor>,
        fact: FinalFactReader,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        evc: EvaluatedCleanAction
    ): List<EvaluatedCleanAction> {
        val (cleanedFacts, factCleaned) = clearPosition(accessors, fact.factAp)

        val result = mutableListOf<EvaluatedCleanAction>()
        if (factCleaned) {
            val actionInfo = EvaluatedCleanAction.ActionInfo(rule, action)
            result += EvaluatedCleanAction(null, actionInfo, evc)
        }

        return cleanedFacts.mapTo(result) { cleanedFact ->
            val resultFact = fact.replaceFact(cleanedFact)
            val actionInfo = EvaluatedCleanAction.ActionInfo(rule, action)
            EvaluatedCleanAction(resultFact, actionInfo, evc)
        }
    }

    private fun clearPosition(accessors: List<Accessor>, fact: FinalFactAp): Pair<List<FinalFactAp>, Boolean> {
        val head = accessors.first()
        val tail = accessors.drop(1)
        if (tail.isEmpty()) {
            if (fact.startsWithAccessor(AnyAccessor)) {
                val factAfterAny = fact.readAccessor(AnyAccessor)
                    ?: error("Impossible")

                val clearedAfterAny = factAfterAny.clearAccessor(head)
                val restoredAfterAny = clearedAfterAny?.prependAccessor(AnyAccessor)

                val factWithoutAny = fact.clearAccessor(AnyAccessor)
                val cleanedWithoutAny = factWithoutAny?.clearAccessor(head)

                val cleaned = clearedAfterAny != factAfterAny || cleanedWithoutAny != factWithoutAny

                return listOfNotNull(restoredAfterAny, cleanedWithoutAny) to cleaned
            }

            if (!fact.startsWithAccessor(head)) {
                return listOf(fact) to false
            }

            val clearedFact = fact.clearAccessor(head)
            val cleaned = clearedFact != fact

            return listOfNotNull(clearedFact) to cleaned
        }

        val child = fact.readAccessor(head)
            ?: return listOf(fact) to false

        val remaining = listOfNotNull(fact.clearAccessor(head))
        val (cleanChild, childCleaned) = clearPosition(tail, child)
        val cleanChildWithAccessor = cleanChild.map { it.prependAccessor(head) }
        val fullFact = remaining + cleanChildWithAccessor

        return fullFact to childCleaned
    }

    private fun PositionAccess.accessorList(): List<Accessor> = when (this) {
        is PositionAccess.Simple -> emptyList()
        is PositionAccess.Complex -> base.accessorList() + accessor
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
