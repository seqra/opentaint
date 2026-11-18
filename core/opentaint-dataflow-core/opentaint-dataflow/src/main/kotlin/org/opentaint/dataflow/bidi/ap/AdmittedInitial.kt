package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase

/** An entry command. Layer is not part of the interned premise identity. */
data class AdmittedInitial(val initial: InitialAp, val layer: Layer)

/** Query-local output; inspecting coverage does not intern hypothetical initials. */
data class InitialEmission(val pattern: Pattern, val layer: Layer)

private fun intrinsicInitialLayer(tail: Tail, mark: MarkSlot, zero: Boolean): Layer = when {
    zero -> Layer.NORMAL
    tail == Tail.ANY -> Layer.DEMAND
    tail == Tail.STAR && mark is MarkSlot.Concrete -> Layer.DEMAND
    else -> Layer.NORMAL
}

fun intrinsicInitialLayer(initial: InitialAp): Layer =
    intrinsicInitialLayer(initial.tail, initial.mark, initial.isZero)

fun intrinsicInitialLayer(pattern: Pattern): Layer =
    intrinsicInitialLayer(pattern.fact.tail, pattern.fact.mark, pattern.fact.base == AccessPathBase.Zero)

/** Concrete data inherits its actual support. FLOW and ZERO keep their old entry policy. */
fun admissionLayer(emitted: Pattern, actual: Pattern, supplied: Layer): Layer {
    val intrinsic = intrinsicInitialLayer(emitted)
    if (emitted.fact.base == AccessPathBase.Zero || emitted.fact.mark is MarkSlot.Star) return intrinsic
    val loss = emitted.fact.tail == Tail.EXACT && actual.fact.tail == Tail.ANY
    return intrinsic or (supplied == Layer.DEMAND || loss)
}

/** Canonicalize before seen-bit admission, including intrinsic STAR and run-1 policies. */
fun canonicalAdmission(initial: InitialAp, supplied: Layer, mode: ApMode? = null): AdmittedInitial {
    val ordinary = intrinsicInitialLayer(initial) or (supplied == Layer.DEMAND)
    val run1Demand = mode?.run1 == true && (initial.base == STATIC ||
        !initial.isZero && initial.mark is MarkSlot.Concrete && mode.markMode == MarkMode.GROUP)
    return AdmittedInitial(initial, ordinary or run1Demand)
}

fun existingZeroAdmission(initial: InitialAp): AdmittedInitial {
    require(initial.isZero) { "ZERO admission requires the existing canonical ZERO key" }
    return AdmittedInitial(initial, Layer.NORMAL)
}
