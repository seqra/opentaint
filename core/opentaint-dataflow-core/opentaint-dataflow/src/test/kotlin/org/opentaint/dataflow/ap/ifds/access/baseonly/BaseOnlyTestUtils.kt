package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX

/** Test-only reference join for differential and relation assertions. */
internal fun canonicalJoin(left: BaseOnlyAccess, right: BaseOnlyAccess): Set<BaseOnlyAccess> {
    BaseOnlyAccessOps.requireCanonical(left)
    BaseOnlyAccessOps.requireCanonical(right)
    if (left == right || BaseOnlyAccessOps.covers(left, right)) return setOf(left)
    if (BaseOnlyAccessOps.covers(right, left)) return setOf(right)

    if (left.staticIdx == right.staticIdx &&
        left.fieldIdx == right.fieldIdx &&
        left.suffixIdx == right.suffixIdx &&
        left.hasSemanticMark &&
        left.valueAccessorState != right.valueAccessorState
    ) return setOf(left, right)

    if (left.staticIdx != right.staticIdx ||
        left.staticIdx == ABSTRACT_MARK || right.staticIdx == ABSTRACT_MARK
    ) return setOf(ABSTRACT_EMPTY_ACCESS)

    val staticIdx = left.staticIdx
    if (left.fieldIdx == ABSTRACT_MARK || right.fieldIdx == ABSTRACT_MARK) {
        return setOf(packBaseOnlyAccess(staticIdx, ABSTRACT_MARK, NO_ACCESSOR))
    }

    val fieldIdx = if (left.fieldIdx == right.fieldIdx) left.fieldIdx else NO_ACCESSOR
    val suffixIdx = if (left.suffixIdx == right.suffixIdx) left.suffixIdx else ABSTRACT_MARK
    if (suffixIdx >= 0 && suffixIdx != FINAL_ACCESSOR_IDX &&
        left.valueAccessorState != right.valueAccessorState
    ) {
        return setOf(
            packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, left.valueAccessorState),
            packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx, right.valueAccessorState),
        )
    }
    return setOf(packBaseOnlyAccess(staticIdx, fieldIdx, suffixIdx))
}
