package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor

fun slotOfIdx(idx: AccessorIdx): Int = when {
    idx.isStaticAccessor() -> 0
    idx.isFieldAccessor() || idx == ELEMENT_ACCESSOR_IDX -> 1
    else -> 2
}

fun IntOpenHashSet.excludesIdx(idx: AccessorIdx): Boolean =
    contains(idx) || (idx.isTypeInfoAccessor() && contains(TYPE_INFO_GROUP_ACCESSOR_IDX))
