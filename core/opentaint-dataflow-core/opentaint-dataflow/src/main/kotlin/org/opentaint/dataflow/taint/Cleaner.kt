package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyMatchMode
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

/**
 * Whether an EXACT cleaner leaves a mark sitting under an `[any]` alone. See the long note at its
 * use site in [cleanConcrete].
 *
 * Read from [AnyMatchMode], not parsed here. This used to be its own `System.getProperty` on this
 * file, which made it the one reader of the literal/denotational decision that no per-instance
 * override could reach: `FinalFactAp.cleanConcrete` has no `ApManager` in scope, so a manager built
 * with `literalAnyMatch = false` still got literal-era cleaning in the same JVM.
 */
private val EXACT_CLEANER_KEEPS_ANY: Boolean get() = AnyMatchMode.exactCleanerKeepsAny

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

                    // An EXACT cleaner cleans `x.![m]` and nothing deeper, but the fact's `[any]`
                    // node carries the mark for EVERY step count at once: zero steps (which the
                    // cleaner does remove) and one-or-more (which it must not). `[any]` is
                    // zero-or-more, there is no one-or-more accessor, and the mark sits on a single
                    // node -- so the two readings cannot be separated in this representation.
                    //
                    // Clearing keeps the cleaner precise and silently drops every >=1-step reading.
                    // That was survivable only while `TreeInitialFactAbstraction`'s R3c/R4 ladder
                    // materialised concrete rungs under the `[any]` for the survivors to live on.
                    // With the ladder gone (see the literal-matching design) clearing collapses the
                    // whole fact, and `CleanerDslAnalysisTest`'s AnyField matrix loses EVERY finding
                    // at every depth -- measured, and attributed with
                    // `-Dopentaint.literalAnyMatch.premises`.
                    //
                    // So keep the branch. The cost is exactly one shape: a plain sink reading the
                    // value itself still sees a mark the cleaner nominally removed
                    // (`AnyField-Plain-Plain-field-depth0`). That is the FP direction, it is the
                    // already-accepted "a cleaner does not clean an abstract fact" line, and the
                    // 688-test rule-level suite is byte-identical either way. Losing a finding is
                    // not acceptable; being coarse here is.
                    val clearedAfterAny =
                        if (EXACT_CLEANER_KEEPS_ANY) factAfterAny else factAfterAny.clearAccessor(head)
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
