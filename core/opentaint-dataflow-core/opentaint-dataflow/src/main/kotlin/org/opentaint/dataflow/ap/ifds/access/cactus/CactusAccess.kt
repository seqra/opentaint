package org.opentaint.dataflow.ap.ifds.access.cactus

/**
 * Joins alternative Cactus facts. Shape and residual any-field cleaners are one semantic value:
 * the shape grows, while a cleaner survives only when every alternative performed it.
 */
internal fun CactusFinalAccess.mergeAdd(other: CactusFinalAccess): CactusFinalAccess {
    val mergedAccess = access.mergeAdd(other.access)
    val mergedCleaners = cleanerEffects join other.cleanerEffects
    return if (mergedAccess === access && mergedCleaners === cleanerEffects) {
        this
    } else {
        CactusFinalAccess(mergedAccess, mergedCleaners)
    }
}

/**
 * The joined value and the part consumers must process again.
 *
 * A cleaner-state change affects the whole access value, so its delta is the complete join.
 */
internal fun CactusFinalAccess.mergeAddDelta(
    other: CactusFinalAccess,
): Pair<CactusFinalAccess, CactusFinalAccess?> {
    val (mergedAccess, accessDelta) = access.mergeAddDelta(other.access)
    val mergedCleaners = cleanerEffects join other.cleanerEffects
    val cleanersChanged = mergedCleaners !== cleanerEffects

    if (accessDelta == null && !cleanersChanged) return this to null

    val merged = CactusFinalAccess(mergedAccess, mergedCleaners)
    val delta = if (cleanersChanged) {
        merged
    } else {
        CactusFinalAccess(accessDelta!!, mergedCleaners)
    }
    return merged to delta
}

internal fun CactusFinalAccess.filterStartsWith(
    initial: CactusInitialAccess,
): CactusFinalAccess? =
    access.filterStartsWith(initial.access)?.let { CactusFinalAccess(it, cleanerEffects) }
