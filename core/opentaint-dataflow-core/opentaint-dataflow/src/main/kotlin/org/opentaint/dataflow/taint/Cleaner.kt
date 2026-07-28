package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
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

        if (!from.isAnyFieldCleaner() &&
            !fact.containsPositionWithTaintMark(from, markRestriction)
        ) {
            return listOf(evc)
        }

        val cleanAccessors = from.accessorList() + markRestriction
        return cleanAccessors(cleanAccessors, fact, rule, action, evc)
    }

    /**
     * An any-field cleaner is a persistent effect on the represented fact, even when no matching
     * concrete path exists yet. Concrete cleaners instead query [FinalFactReader] first so a
     * missing path becomes a demand refinement.
     */
    private fun PositionAccess.isAnyFieldCleaner(): Boolean =
        this is PositionAccess.Complex && accessor is AnyAccessor && base is PositionAccess.Simple

    private fun cleanAccessors(
        accessors: List<Accessor>,
        fact: FinalFactReader,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        evc: EvaluatedCleanAction
    ): List<EvaluatedCleanAction> {
        val cleaned = fact.factAp.clean(accessors)

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
