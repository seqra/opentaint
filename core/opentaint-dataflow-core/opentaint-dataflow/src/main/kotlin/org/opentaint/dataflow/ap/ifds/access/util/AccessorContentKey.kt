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
 * Components are length-framed, so even unusual bytecode identifiers cannot make two
 * distinct fields collide. Ordering uses [Accessor.compareTo]; this key is for hashing and
 * serialization. The `when` is exhaustive on purpose -- a new accessor kind must fail
 * compilation here rather than silently fall back to a process-specific representation.
 */
internal fun Accessor.contentKey(): String = when (this) {
    is FieldAccessor -> "F${className.framed()}${fieldName.framed()}${fieldType.framed()}"
    is ClassStaticAccessor -> "S${typeName.framed()}"
    is TaintMarkAccessor -> "T${mark.framed()}"
    is TypeInfoAccessor -> "Y${typeName.framed()}"
    ElementAccessor -> "E"
    FinalAccessor -> "D"
    AnyAccessor -> "A"
    ValueAccessor -> "V"
    TypeInfoGroupAccessor -> "G"
}

private fun String.framed(): String = "$length:$this"
