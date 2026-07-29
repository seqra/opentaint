package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx

/**
 * Marks excluded from future materialization of an AnyField abstraction.
 *
 * An AnyField cleaner removes every currently materialized matching mark and records here what
 * must remain excluded if the fact later grows. Tree stores the value on abstract nodes; Automata
 * and Cactus store it beside their final access values. Initial facts never carry it.
 *
 * Each mark carries the minimum relative depth below the AnyField at which it is excluded:
 *
 *  - [marksFromDepth1] applies to a direct mark child and everything deeper.
 *  - [marksFromDepth2] preserves a direct mark child and applies after one intervening accessor.
 *
 * Arrays are sorted and disjoint. [create] returns `null` for an empty tree annotation; root-only
 * representations use [Empty] as their explicit neutral value.
 */
class AnyFieldMarkExclusions private constructor(
    @JvmField val marksFromDepth1: IntArray,
    @JvmField val marksFromDepth2: IntArray,
) {
    private val hash: Int = marksFromDepth1.contentHashCode() * 31 + marksFromDepth2.contentHashCode()

    override fun hashCode(): Int = hash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is AnyFieldMarkExclusions) return false
        if (hash != other.hash) return false
        return marksFromDepth1.contentEquals(other.marksFromDepth1)
            && marksFromDepth2.contentEquals(other.marksFromDepth2)
    }

    operator fun contains(mark: AccessorIdx): Boolean =
        marksFromDepth1.binarySearch(mark) >= 0 || marksFromDepth2.binarySearch(mark) >= 0

    val isEmpty: Boolean
        get() = marksFromDepth1.isEmpty() && marksFromDepth2.isEmpty()

    /** A base-level any-field clean starts applying below one concrete accessor. */
    fun add(mark: AccessorIdx): AnyFieldMarkExclusions = addMarkFromDepth2(mark)

    internal infix fun then(other: AnyFieldMarkExclusions): AnyFieldMarkExclusions =
        then(this, other) ?: Empty

    internal infix fun join(other: AnyFieldMarkExclusions): AnyFieldMarkExclusions =
        join(this, other) ?: Empty

    private fun allMarks(): IntArray = (marksFromDepth1 + marksFromDepth2).also { it.sort() }

    /**
     * The claim as seen from any position at least one accessor below the annotated node:
     * everything below such a position is at depth >= 2 relative to the annotated node, so every
     * claimed mark — depth-1 and depth-2 alike — applies from relative depth 1 there.
     */
    fun collapseToDepth1(): AnyFieldMarkExclusions =
        if (marksFromDepth2.isEmpty()) this else AnyFieldMarkExclusions(allMarks(), EMPTY)

    override fun toString(): String = buildString {
        append("!*{d1=")
        append(marksFromDepth1.joinToString(","))
        append(";d2=")
        append(marksFromDepth2.joinToString(","))
        append("}")
    }

    companion object {
        private val EMPTY = IntArray(0)
        val Empty = AnyFieldMarkExclusions(EMPTY, EMPTY)

        /**
         * [marksFromDepth1] and [marksFromDepth2] must each be sorted; a mark present in both is
         * kept at depth 1. Alternative executions must instead combine through [join], which
         * resolves the conflict in the weaker direction.
         */
        fun create(marksFromDepth1: IntArray, marksFromDepth2: IntArray): AnyFieldMarkExclusions? {
            val d2 = if (marksFromDepth2.any { marksFromDepth1.binarySearch(it) >= 0 }) {
                marksFromDepth2.filter { marksFromDepth1.binarySearch(it) < 0 }.toIntArray()
            } else {
                marksFromDepth2
            }

            if (marksFromDepth1.isEmpty() && d2.isEmpty()) return null
            return AnyFieldMarkExclusions(marksFromDepth1, d2)
        }

        private fun fromDepth1(mark: AccessorIdx): AnyFieldMarkExclusions = AnyFieldMarkExclusions(intArrayOf(mark), EMPTY)

        private fun fromDepth2(mark: AccessorIdx): AnyFieldMarkExclusions = AnyFieldMarkExclusions(EMPTY, intArrayOf(mark))

        fun AnyFieldMarkExclusions?.addMarkFromDepth1(mark: AccessorIdx): AnyFieldMarkExclusions {
            if (this == null) return fromDepth1(mark)
            if (marksFromDepth1.binarySearch(mark) >= 0) return this
            // depth 1 is the stronger claim: it absorbs a depth-2 entry for the same mark
            val d1 = (marksFromDepth1 + mark).also { it.sort() }
            val d2 = if (marksFromDepth2.binarySearch(mark) >= 0) {
                marksFromDepth2.filter { it != mark }.toIntArray()
            } else {
                marksFromDepth2
            }
            return AnyFieldMarkExclusions(d1, d2)
        }

        fun AnyFieldMarkExclusions?.addMarkFromDepth2(mark: AccessorIdx): AnyFieldMarkExclusions {
            if (this == null) return fromDepth2(mark)
            if (contains(mark)) return this
            val d2 = (marksFromDepth2 + mark).also { it.sort() }
            return AnyFieldMarkExclusions(marksFromDepth1, d2)
        }

        /**
         * The join of two alternative executions meeting at the SAME abstract node: a mark
         * survives only when both alternatives exclude it, and at the weaker of the two depths
         * (max — a claim both alternatives make only from depth 2 cannot be strengthened to
         * depth 1).
         *
         * The abstraction state itself joins with "not abstract" as the identity: when only one
         * operand is abstract, all abstraction (and its annotation) comes from that operand —
         * callers handle that case and reach here only with two abstract operands.
         */
        fun join(a: AnyFieldMarkExclusions?, b: AnyFieldMarkExclusions?): AnyFieldMarkExclusions? {
            if (a == null || b == null) return null
            if (a == b) return a

            val d1 = a.marksFromDepth1.filter { b.marksFromDepth1.binarySearch(it) >= 0 }.toIntArray()
            val d2 = mutableListOf<Int>()
            for (mark in a.allMarks()) {
                if (d1.binarySearch(mark) >= 0) continue
                if (b.contains(mark)) d2.add(mark)
            }
            return create(d1, d2.toIntArray())
        }

        /**
         * Sequential composition of two claims that BOTH hold: the caller had already cleaned one
         * mark when the callee's summary, whose exit abstraction continues the same object,
         * cleaned another. Marks union; a mark claimed at both depths keeps the stronger (min —
         * depth 1 covers everything depth 2 does).
         */
        fun then(a: AnyFieldMarkExclusions?, b: AnyFieldMarkExclusions?): AnyFieldMarkExclusions? {
            if (a == null) return b
            if (b == null) return a
            if (a == b) return a

            val d1 = (a.marksFromDepth1.toSet() + b.marksFromDepth1.toSet()).toIntArray().also { it.sort() }
            val d2 = (a.marksFromDepth2.toSet() + b.marksFromDepth2.toSet())
                .filter { d1.binarySearch(it) < 0 }
                .toIntArray().also { it.sort() }
            return create(d1, d2)
        }
    }
}

internal fun AnyFieldMarkExclusions.forExclusions(
    exclusions: ExclusionSet,
): AnyFieldMarkExclusions =
    if (exclusions is ExclusionSet.Universe) AnyFieldMarkExclusions.Empty else this
