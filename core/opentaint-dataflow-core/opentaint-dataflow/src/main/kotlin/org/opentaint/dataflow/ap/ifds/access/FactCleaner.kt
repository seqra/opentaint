package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor

/**
 * Representation-neutral traversal for concrete cleaner positions.
 *
 * Only the residual effect of `[any].![mark]` is representation-specific, because it must survive
 * future materialization of an abstract fact.
 */
internal fun FinalFactAp.clean(
    accessors: List<Accessor>,
    cleanAnyField: (TaintMarkAccessor) -> FinalFactAp.CleanResult,
): FinalFactAp.CleanResult {
    require(accessors.isNotEmpty()) { "A fact cleaner needs a non-empty access path" }

    if (accessors.size == 2 && accessors.first() is AnyAccessor) {
        val mark = accessors.last()
        if (mark is TaintMarkAccessor) return cleanAnyField(mark)
    }

    return cleanConcrete(accessors)
}

private fun FinalFactAp.cleanConcrete(accessors: List<Accessor>): FinalFactAp.CleanResult {
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
    val cleanedChild = child.clean(tail)
    val restoredChildren = cleanedChild.survivingFacts.map { it.prependAccessor(head) }
    return FinalFactAp.CleanResult(
        remaining + restoredChildren,
        removedAlternative = cleanedChild.removedAlternative,
    )
}
