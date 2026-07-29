package org.opentaint.dataflow.ap.ifds.access.cactus

/**
 * Joins alternative Cactus facts. Shape and AnyField mark exclusions are one semantic value:
 * shape grows, while a mark exclusion survives only when every alternative establishes it.
 */
internal fun CactusFinalAccess.mergeAdd(other: CactusFinalAccess): CactusFinalAccess {
    val mergedAccess = access.mergeAdd(other.access)
    val mergedMarkExclusions = anyFieldMarkExclusions join other.anyFieldMarkExclusions
    return if (mergedAccess === access && mergedMarkExclusions == anyFieldMarkExclusions) {
        this
    } else {
        CactusFinalAccess(mergedAccess, mergedMarkExclusions)
    }
}

/**
 * The joined value and the part consumers must process again.
 *
 * An AnyField mark-exclusion change affects the whole access value, so its delta is the complete
 * join.
 */
internal fun CactusFinalAccess.mergeAddDelta(
    other: CactusFinalAccess,
): Pair<CactusFinalAccess, CactusFinalAccess?> {
    val (mergedAccess, accessDelta) = access.mergeAddDelta(other.access)
    val mergedMarkExclusions = anyFieldMarkExclusions join other.anyFieldMarkExclusions
    val exclusionsChanged = mergedMarkExclusions != anyFieldMarkExclusions

    if (accessDelta == null && !exclusionsChanged) return this to null

    val merged = CactusFinalAccess(mergedAccess, mergedMarkExclusions)
    val delta = if (exclusionsChanged) {
        merged
    } else {
        CactusFinalAccess(accessDelta!!, mergedMarkExclusions)
    }
    return merged to delta
}

internal fun CactusFinalAccess.filterStartsWith(
    initial: CactusInitialAccess,
): CactusFinalAccess? =
    access.filterStartsWith(initial)?.let { CactusFinalAccess(it, anyFieldMarkExclusions) }
