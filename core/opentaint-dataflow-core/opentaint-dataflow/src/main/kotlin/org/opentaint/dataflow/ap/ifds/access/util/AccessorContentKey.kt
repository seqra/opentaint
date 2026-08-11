package org.opentaint.dataflow.ap.ifds.access.util

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor

/**
 * The full content of an accessor as a string, injective across kinds (distinct prefixes)
 * and within a kind (every identity-bearing field is included; [Accessor.toString] is not
 * enough -- [FieldAccessor] prints neither its package nor its field type).
 *
 * This is key MATERIAL for canonical fact keys and interner dumps. It is NOT an ordering:
 * every ordering decision uses [Accessor]'s own [Comparable] implementation, which is the
 * single canonical order. The `when` is exhaustive on purpose -- a new accessor kind must
 * fail compilation here rather than silently fall back to a non-injective representation.
 */
internal fun Accessor.contentKey(): String = when (this) {
    is FieldAccessor -> "F|$className|$fieldName|$fieldType"
    is ClassStaticAccessor -> "S|$typeName"
    is TaintMarkAccessor -> "T|$mark"
    is TypeInfoAccessor -> "Y|$typeName"
    ElementAccessor -> "[*]"
    FinalAccessor -> "[$]"
    AnyAccessor -> "[any]"
    ValueAccessor -> "[value]"
    TypeInfoGroupAccessor -> "[type]"
}
