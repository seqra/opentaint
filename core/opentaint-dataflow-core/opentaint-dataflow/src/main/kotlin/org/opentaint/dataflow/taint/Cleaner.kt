package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.TaintCleanReach

class TaintCleanActionEvaluator {
    fun removeAllFacts(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ): List<EvaluatedCleanAction> {
        val fact = evc.fact ?: return listOf(evc)
        return clean(Cleaner.AllMarks(from), fact, rule, action, evc)
    }

    fun removeFinalFact(
        evc: EvaluatedCleanAction,
        from: PositionAccess,
        markRestriction: TaintMarkAccessor,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        reach: TaintCleanReach,
    ): List<EvaluatedCleanAction> {
        val fact = evc.fact ?: return listOf(evc)
        return clean(Cleaner.Mark(from, markRestriction, reach), fact, rule, action, evc)
    }

    private fun clean(
        cleaner: Cleaner,
        fact: FinalFactReader,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        evc: EvaluatedCleanAction
    ): List<EvaluatedCleanAction> {
        val cleaned = fact.clean(cleaner)
            ?: return listOf(evc)

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

    private fun FinalFactReader.clean(cleaner: Cleaner): CleanResult? {
        if (cleaner.position.base() != factAp.base) {
            return null
        }

        if (cleaner is Cleaner.AllMarks || !cleaner.position.hasAnyField()) {
            val present = when (cleaner) {
                is Cleaner.AllMarks -> containsPosition(cleaner.position)
                is Cleaner.Mark -> containsPositionWithTaintMark(cleaner.position, cleaner.mark)
            }
            if (!present) return null
        }

        return factAp.clean(cleaner)
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

sealed interface Cleaner {
    val position: PositionAccess

    fun replacePosition(newPosition: PositionAccess): Cleaner

    data class AllMarks(
        override val position: PositionAccess,
    ) : Cleaner {
        override fun replacePosition(newPosition: PositionAccess): Cleaner = copy(position = newPosition)
    }

    data class Mark(
        override val position: PositionAccess,
        val mark: TaintMarkAccessor,
        val reach: TaintCleanReach,
    ) : Cleaner {
        override fun replacePosition(newPosition: PositionAccess): Cleaner = copy(position = newPosition)
    }
}

data class CleanResult(
    val survivingFacts: List<FinalFactAp>,
    val removedAlternative: Boolean,
)

fun FinalFactAp.clean(cleaner: Cleaner): CleanResult {
    if (cleaner is Cleaner.Mark) {
        val positionAccessors = cleaner.position.accessors()
        if (positionAccessors.size == 1 && positionAccessors.single() is AnyAccessor) {
            return cleanAnyFieldMark(cleaner.mark, keepStartAccessor = true)
        }
    }

    return cleanConcrete(cleaner)
}

private fun Cleaner.removePrefix(prefix: Accessor): Cleaner {
    val remainingPosition = position.removePrefix(prefix)
    return replacePosition(remainingPosition)
}

private fun Cleaner.accessors(): List<Accessor> =
    position.accessors() + if (this is Cleaner.Mark) listOf(mark) else emptyList()

private fun FinalFactAp.cleanConcrete(cleaner: Cleaner): CleanResult {
    val accessors = cleaner.accessors()
    if (accessors.isEmpty()) {
        check(cleaner is Cleaner.AllMarks)
        return CleanResult(emptyList(), removedAlternative = true)
    }

    val head = accessors.first()
    val tail = accessors.drop(1)
    if (tail.isEmpty()) {
        if (cleaner is Cleaner.Mark && startsWithAccessor(AnyAccessor)) {
            when (cleaner.reach) {
                TaintCleanReach.ExactAndAnyField -> {
                    return cleanAnyFieldMark(cleaner.mark, keepStartAccessor = false)
                }

                TaintCleanReach.Exact -> {
                    val factAfterAny = readAccessor(AnyAccessor)
                        ?: error("Impossible")

                    val clearedAfterAny = factAfterAny.clearAccessor(head)
                    val restoredAfterAny = clearedAfterAny?.prependAccessor(AnyAccessor)

                    val factWithoutAny = clearAccessor(AnyAccessor)
                    val cleanedWithoutAny = factWithoutAny?.clearAccessor(head)

                    return CleanResult(
                        listOfNotNull(restoredAfterAny, cleanedWithoutAny),
                        removedAlternative = clearedAfterAny != factAfterAny || cleanedWithoutAny != factWithoutAny,
                    )
                }
            }
        }

        if (!startsWithAccessor(head)) {
            return CleanResult(listOf(this), removedAlternative = false)
        }

        val cleared = clearAccessor(head)
        return CleanResult(
            listOfNotNull(cleared),
            removedAlternative = cleared != this,
        )
    }

    val child = readAccessor(head)
        ?: return CleanResult(listOf(this), removedAlternative = false)

    val remaining = listOfNotNull(clearAccessor(head))
    val cleanedChild = child.clean(cleaner.removePrefix(head))
    val restoredChildren = cleanedChild.survivingFacts.map { it.prependAccessor(head) }
    return CleanResult(
        remaining + restoredChildren,
        removedAlternative = cleanedChild.removedAlternative,
    )
}

private fun FinalFactAp.cleanAnyFieldMark(
    mark: TaintMarkAccessor,
    keepStartAccessor: Boolean,
): CleanResult {
    val cleaned = clearAllAccessorOccurrences(mark, keepStartAccessor)
        ?: return CleanResult(emptyList(), removedAlternative = true)
    return CleanResult(
        survivingFacts = listOf(cleaned),
        removedAlternative = !keepStartAccessor && cleaned != this,
    )
}
