package org.opentaint.dataflow.ap.ifds.access.automata

/** Joins alternative final accesses as one complete representation value. */
internal fun AutomataFinalAccess.mergeAdd(
    other: AutomataFinalAccess,
): AutomataFinalAccess {
    val mergedAccess =
        if (access.containsAll(other.access)) access else access.merge(other.access)
    val mergedMarkExclusions = anyFieldMarkExclusions join other.anyFieldMarkExclusions

    return if (mergedAccess === access && mergedMarkExclusions === anyFieldMarkExclusions) {
        this
    } else {
        AutomataFinalAccess(mergedAccess, mergedMarkExclusions)
    }
}
