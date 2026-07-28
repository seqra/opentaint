package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx

/**
 * Excluded-mark annotation of an ABSTRACT [AccessTree.AccessNode]: a starred sanitizer's residual
 * claim that a taint mark is removed from everything that later materializes below this node — by a
 * summary delta concatenated onto it, or by demand-driven refinement growing through it.
 *
 * The claim lives on the abstract node and nowhere else. The concrete part of a fact is closed
 * (every path enumerated), so a starred clean deletes concrete mark nodes outright and needs no
 * residue there; an abstract node is the one place the fact can still grow, so it is the one place
 * the claim is needed. Because the annotation is part of the node, a `prependAccessor` carries it
 * down with the path and a sibling branch simply never meets it — discrimination that a flat
 * edge-level cleaner flag cannot express.
 *
 * Each mark carries the minimal RELATIVE depth below the annotated node at which it is excluded:
 *
 *  - [marksFromDepth1] — excluded everywhere strictly below the node, including a mark that
 *    materializes as its direct child. Used for abstract nodes that already sit at least one
 *    accessor below the cleaned base: everything below them is "under a field of the base", which
 *    is exactly what `base.*` covers.
 *  - [marksFromDepth2] — excluded only below at least one further accessor. Used for the abstract
 *    node at the cleaned base itself: `base.*` does not cover the mark carried by the base
 *    directly (that is the rule's `base` clean action's job), so a direct mark-child of this node
     *    survives.
 *
 * Instances are canonical: arrays are sorted, disjoint, and never both empty ([create] returns
 * null instead — "abstract with no exclusions" is represented by the absence of the annotation).
 */
class AbstractionExclusions private constructor(
    @JvmField val marksFromDepth1: IntArray,
    @JvmField val marksFromDepth2: IntArray,
) {
    private val hash: Int = marksFromDepth1.contentHashCode() * 31 + marksFromDepth2.contentHashCode()

    override fun hashCode(): Int = hash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is AbstractionExclusions) return false
        if (hash != other.hash) return false
        return marksFromDepth1.contentEquals(other.marksFromDepth1)
            && marksFromDepth2.contentEquals(other.marksFromDepth2)
    }

    operator fun contains(mark: AccessorIdx): Boolean =
        marksFromDepth1.binarySearch(mark) >= 0 || marksFromDepth2.binarySearch(mark) >= 0

    private fun allMarks(): IntArray = (marksFromDepth1 + marksFromDepth2).also { it.sort() }

    /**
     * The claim as seen from any position at least one accessor below the annotated node:
     * everything below such a position is at depth >= 2 relative to the annotated node, so every
     * claimed mark — depth-1 and depth-2 alike — applies from relative depth 1 there.
     */
    fun collapseToDepth1(): AbstractionExclusions =
        if (marksFromDepth2.isEmpty()) this else AbstractionExclusions(allMarks(), EMPTY)

    override fun toString(): String = buildString {
        append("!*{d1=")
        append(marksFromDepth1.joinToString(","))
        append(";d2=")
        append(marksFromDepth2.joinToString(","))
        append("}")
    }

    companion object {
        private val EMPTY = IntArray(0)

        /**
         * [marksFromDepth1] and [marksFromDepth2] must each be sorted; a mark present in both is
         * kept at depth 1. Alternative executions must instead combine through [join], which
         * resolves the conflict in the weaker direction.
         */
        fun create(marksFromDepth1: IntArray, marksFromDepth2: IntArray): AbstractionExclusions? {
            val d2 = if (marksFromDepth2.any { marksFromDepth1.binarySearch(it) >= 0 }) {
                marksFromDepth2.filter { marksFromDepth1.binarySearch(it) < 0 }.toIntArray()
            } else {
                marksFromDepth2
            }

            if (marksFromDepth1.isEmpty() && d2.isEmpty()) return null
            return AbstractionExclusions(marksFromDepth1, d2)
        }

        private fun fromDepth1(mark: AccessorIdx): AbstractionExclusions = AbstractionExclusions(intArrayOf(mark), EMPTY)

        private fun fromDepth2(mark: AccessorIdx): AbstractionExclusions = AbstractionExclusions(EMPTY, intArrayOf(mark))

        fun AbstractionExclusions?.addMarkFromDepth1(mark: AccessorIdx): AbstractionExclusions {
            if (this == null) return fromDepth1(mark)
            if (marksFromDepth1.binarySearch(mark) >= 0) return this
            // depth 1 is the stronger claim: it absorbs a depth-2 entry for the same mark
            val d1 = (marksFromDepth1 + mark).also { it.sort() }
            val d2 = if (marksFromDepth2.binarySearch(mark) >= 0) {
                marksFromDepth2.filter { it != mark }.toIntArray()
            } else {
                marksFromDepth2
            }
            return AbstractionExclusions(d1, d2)
        }

        fun AbstractionExclusions?.addMarkFromDepth2(mark: AccessorIdx): AbstractionExclusions {
            if (this == null) return fromDepth2(mark)
            if (contains(mark)) return this
            val d2 = (marksFromDepth2 + mark).also { it.sort() }
            return AbstractionExclusions(marksFromDepth1, d2)
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
        fun join(a: AbstractionExclusions?, b: AbstractionExclusions?): AbstractionExclusions? {
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
        fun then(a: AbstractionExclusions?, b: AbstractionExclusions?): AbstractionExclusions? {
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
