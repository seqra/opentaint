package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor

sealed interface PositionAccess {
    data class Simple(val base: AccessPathBase) : PositionAccess
    data class Complex(val base: PositionAccess, val accessor: Accessor) : PositionAccess
}

fun PositionAccess.base(): AccessPathBase = when (this) {
    is PositionAccess.Complex -> this.base.base()
    is PositionAccess.Simple -> this.base
}

private fun PositionAccess.baseIsResult(): Boolean = when (this) {
    is PositionAccess.Complex -> base.baseIsResult()
    is PositionAccess.Simple -> base is AccessPathBase.Return
}

fun PositionAccess.withPrefix(prefix: Accessor): PositionAccess = when (this) {
    is PositionAccess.Complex -> PositionAccess.Complex(base.withPrefix(prefix), accessor)
    is PositionAccess.Simple -> PositionAccess.Complex(this, prefix)
}

fun PositionAccess.withPrefix(prefix: List<Accessor>): PositionAccess = when (this) {
    is PositionAccess.Complex -> PositionAccess.Complex(base.withPrefix(prefix), accessor)
    is PositionAccess.Simple -> prefix.fold(this as PositionAccess) { res, ac ->
        PositionAccess.Complex(res, ac)
    }
}

fun PositionAccess.withSuffix(suffix: List<Accessor>): PositionAccess =
    suffix.fold(this) { res, ac -> PositionAccess.Complex(res, ac) }

fun PositionAccess.removeSuffix(suffix: List<Accessor>): PositionAccess {
    var result = this
    for (ac in suffix.asReversed()) {
        check(result is PositionAccess.Complex && result.accessor == ac) {
            "Suffix mismatch"
        }
        result = result.base
    }
    return result
}

fun PositionAccess.removePrefix(prefix: Accessor): PositionAccess = when (this) {
    is PositionAccess.Complex -> when (base) {
        is PositionAccess.Complex -> PositionAccess.Complex(base.removePrefix(prefix), accessor)
        is PositionAccess.Simple -> {
            check(accessor == prefix) { "Prefix mismatch" }
            base
        }
    }

    is PositionAccess.Simple -> error("Prefix mismatch")
}
