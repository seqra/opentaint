package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*

/** Check bounded actual run-2 inputs. A correlated field STAR keeps its E.
 * Returns true for a named FULL field and false for an exact class marker.
 * Acceptance does not authorize an initial or add a source/sink literal shape. */
internal fun validateRun2StaticFullInput(ap: ApManager, actual: Pattern, fieldLimit: Int = 1): Boolean {
    require(fieldLimit >= 1) { "The field limit must be positive" }
    val field = validateRun2StaticFullAnchor(ap, actual) ?: return false
    val fact = actual.fact
    val location = if (field) fact.path.drop(1).all { it.isCounted() } &&
        fact.path.count { it.isCounted() } <= fieldLimit &&
        (fact.tail == Tail.EXACT || fact.tail == Tail.ANY || fact.tail == Tail.STAR)
    else fact.path.size == 1 && fact.tail == Tail.EXACT
    val exclusion = actual.exclusion == ExclusionSet.Empty || field && fact.tail == Tail.STAR
    check(location && exclusion) {
        "Unsupported run-2 concrete static input: $actual. " +
            "Expected a named field within limit $fieldLimit with EXACT/ANY and empty field exclusions, " +
            "a named field with correlated STAR and its legal field exclusion, " +
            "or an EXACT class marker with empty field exclusions. Backward MUST is forbidden."
    }
    return field
}

/** Check only the static anchor of a current result. Its existing header stays
 * intact; the bounded backward-input validator separately rejects MUST.
 * Deeper field suffixes are lawful before the normal field cut.
 * Returns true for a named field, false for an exact class marker, null otherwise. */
internal fun validateRun2StaticFullAnchor(ap: ApManager, actual: Pattern): Boolean? {
    if (actual.fact.base != STATIC) return null
    val atom = (actual.fact.mark as? MarkSlot.Concrete)?.mark ?: return null
    if (ap.marks.fullId(atom) == null) return null // GROUP guidance is metadata, not an actual FULL mark.
    val path = actual.fact.path
    val field = path.size >= 2 && path[0].isClass() &&
        ap.accessors.accessor(path[1]) is FieldAccessor
    val exactClass = path.size == 1 && path[0].isClass() && actual.fact.tail == Tail.EXACT
    check(field || exactClass) {
        "Unsupported run-2 concrete static input: $actual. " +
            "Expected a named JVM static field anchor or an EXACT class marker; " +
            "broad root/class marks require a separate query adapter (run1-static-summary-erasure.md section 3)."
    }
    return field
}
