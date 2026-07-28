package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.taint.Cleaner
import org.opentaint.dataflow.taint.accessors
import org.opentaint.dataflow.taint.base
import org.opentaint.dataflow.taint.removePrefix

/**
 * Representation-neutral traversal for concrete cleaner positions.
 *
 * Only the residual effect of `[any].![mark]` is representation-specific, because it must survive
 * future materialization of an abstract fact.
 */
internal fun FinalFactAp.clean(
    cleaner: Cleaner,
    cleanAnyField: (TaintMarkAccessor) -> FinalFactAp.CleanResult,
): FinalFactAp.CleanResult {
    require(cleaner.position.base() == base) { "Cleaner and fact bases must match" }

    if (cleaner is Cleaner.Mark) {
        val positionAccessors = cleaner.position.accessors()
        if (positionAccessors.size == 1 && positionAccessors.single() is AnyAccessor) {
            return cleanAnyField(cleaner.mark)
        }
    }

    return cleanConcrete(cleaner)
}

private fun Cleaner.accessors(): List<Accessor> =
    position.accessors() + if (this is Cleaner.Mark) listOf(mark) else emptyList()

private fun FinalFactAp.cleanConcrete(cleaner: Cleaner): FinalFactAp.CleanResult {
    val accessors = cleaner.accessors()
    if (accessors.isEmpty()) {
        check(cleaner is Cleaner.AllMarks)
        return FinalFactAp.CleanResult(emptyList(), removedAlternative = true)
    }

    val head = accessors.first()
    val tail = accessors.drop(1)
    if (tail.isEmpty()) {
        if (startsWithAccessor(AnyAccessor)) {
            val afterAny = readAccessor(AnyAccessor)
                ?: error("Fact reports an any-field accessor but cannot read it")

            val clearedAfterAny = afterAny.clearAccessor(head)
            val restoredAfterAny = clearedAfterAny?.prependAccessor(AnyAccessor)

            val withoutAny = clearAccessor(AnyAccessor)
            val cleanedWithoutAny = withoutAny?.clearAccessor(head)

            val cleaned = clearedAfterAny != afterAny || cleanedWithoutAny != withoutAny
            return FinalFactAp.CleanResult(
                listOfNotNull(restoredAfterAny, cleanedWithoutAny),
                removedAlternative = cleaned,
            )
        }

        if (!startsWithAccessor(head)) {
            return FinalFactAp.CleanResult(listOf(this), removedAlternative = false)
        }

        val cleared = clearAccessor(head)
        return FinalFactAp.CleanResult(
            listOfNotNull(cleared),
            removedAlternative = cleared != this,
        )
    }

    val child = readAccessor(head)
        ?: return FinalFactAp.CleanResult(listOf(this), removedAlternative = false)

    val remaining = listOfNotNull(clearAccessor(head))
    val cleanedChild = child.clean(cleaner.removePrefix(head))
    val restoredChildren = cleanedChild.survivingFacts.map { it.prependAccessor(head) }
    return FinalFactAp.CleanResult(
        remaining + restoredChildren,
        removedAlternative = cleanedChild.removedAlternative,
    )
}
