package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner

/**
 * Cactus adapter for the shared AnyField mark-exclusion domain.
 *
 * Cactus stores accessors as objects, so this adapter owns the stable interning needed by the
 * compact integer representation without duplicating its join/composition semantics.
 */
@JvmInline
value class CactusAnyFieldMarkExclusions private constructor(
    internal val exclusions: AnyFieldMarkExclusions,
) {
    val isEmpty: Boolean
        get() = exclusions.isEmpty

    fun add(mark: TaintMarkAccessor): CactusAnyFieldMarkExclusions =
        CactusAnyFieldMarkExclusions(exclusions.add(Interner.index(mark)))

    fun excludesFromDepth1(mark: TaintMarkAccessor): Boolean =
        exclusions.marksFromDepth1.binarySearch(Interner.index(mark)) >= 0

    fun collapseToDepth1(): CactusAnyFieldMarkExclusions =
        CactusAnyFieldMarkExclusions(exclusions.collapseToDepth1())

    internal infix fun then(
        other: CactusAnyFieldMarkExclusions,
    ): CactusAnyFieldMarkExclusions =
        CactusAnyFieldMarkExclusions(exclusions then other.exclusions)

    internal infix fun join(
        other: CactusAnyFieldMarkExclusions,
    ): CactusAnyFieldMarkExclusions =
        CactusAnyFieldMarkExclusions(exclusions join other.exclusions)

    internal fun forExclusions(exclusions: ExclusionSet): CactusAnyFieldMarkExclusions =
        if (exclusions is ExclusionSet.Universe) Empty else this

    companion object {
        val Empty = CactusAnyFieldMarkExclusions(AnyFieldMarkExclusions.Empty)

        internal fun fromShared(exclusions: AnyFieldMarkExclusions): CactusAnyFieldMarkExclusions =
            CactusAnyFieldMarkExclusions(exclusions)

        internal fun index(mark: TaintMarkAccessor): AccessorIdx = Interner.index(mark)

        internal fun mark(index: AccessorIdx): TaintMarkAccessor =
            Interner.accessor(index) as? TaintMarkAccessor
                ?: error("Cactus AnyField exclusion is not a taint mark: $index")
    }

    private object Interner {
        private val accessors = AccessorInterner()

        fun index(mark: TaintMarkAccessor): AccessorIdx = accessors.index(mark)

        fun accessor(index: AccessorIdx) = accessors.accessor(index)
    }
}
