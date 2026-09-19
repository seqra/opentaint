package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker

interface AccessorList {
    fun startsWithAccessor(accessor: Accessor): Boolean
    fun getStartAccessors(): Set<Accessor>
    fun getAllAccessors(): Set<Accessor>

    /**
     * `getAllAccessors().contains(accessor)`, without materialising the set.
     *
     * The default is the definition itself, so an implementation that does not override this is
     * unchanged. An override must answer the same predicate -- it exists only to let a
     * representation answer it with an early exit and without allocating.
     */
    fun containsAccessorDeep(accessor: Accessor): Boolean = getAllAccessors().contains(accessor)

    fun isAbstract(): Boolean
}

interface ReadableAccessorList<T : Any> : AccessorList {
    fun readAccessor(accessor: Accessor): T?
}

interface FactAp: AccessorList {
    val base: AccessPathBase
    val exclusions: ExclusionSet

    val size: Int
    val depth: Int
}

interface InitialFactAp : FactAp, ReadableAccessorList<InitialFactAp> {
    fun rebase(newBase: AccessPathBase): InitialFactAp
    fun exclude(accessor: Accessor): InitialFactAp
    fun replaceExclusions(exclusions: ExclusionSet): InitialFactAp

    fun prependAccessor(accessor: Accessor): InitialFactAp
    fun clearAccessor(accessor: Accessor): InitialFactAp?

    interface Delta: ReadableAccessorList<Delta> {
        val isEmpty: Boolean

        fun concat(other: Delta): Delta
    }

    fun splitDelta(other: FinalFactAp): List<Pair<InitialFactAp, Delta>>
    fun concat(delta: Delta): InitialFactAp

    fun contains(factAp: InitialFactAp): Boolean

    fun compatibilityFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactCompatibilityFilter
}

interface FinalFactAp : FactAp, ReadableAccessorList<FinalFactAp> {
    fun rebase(newBase: AccessPathBase): FinalFactAp
    fun exclude(accessor: Accessor): FinalFactAp
    fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp

    fun prependAccessor(accessor: Accessor): FinalFactAp
    fun clearAccessor(accessor: Accessor): FinalFactAp?
    fun removeAbstraction(): FinalFactAp?
    fun abstractOnly(): FinalFactAp

    interface Delta: ReadableAccessorList<Delta> {
        val isEmpty: Boolean

        /**
         * The length of the shortest path from here down to [accessor], or `-1` when no path
         * reaches it -- so `minDepthToAccessor(a) >= 0` is [containsAccessorDeep] for every
         * accessor that occurs as an edge.
         *
         * A step onto a concrete accessor costs one. `[any]` costs nothing: it stands for any
         * number of accessors, so what sits below it is at an unknown distance, and charging a
         * step each would be a number this structure does not hold -- zero is the one choice
         * that keeps the result a lower bound on the true distance. `[any]` is also never a
         * match, matching [containsAccessorDeep].
         *
         * The final marker is a flag on a node rather than an edge, so it is never reached here
         * and answers `-1` where [containsAccessorDeep] answers `true`. Nothing asks: the
         * callers all pass a taint mark.
         */
        fun minDepthToAccessor(accessor: Accessor): Int = genericMinDepthToAccessor(accessor)
    }

    fun delta(other: InitialFactAp): List<Delta>
    fun concat(typeChecker: FactTypeChecker, delta: Delta): FinalFactAp?

    fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp?
    fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp?

    fun contains(factAp: InitialFactAp): Boolean
    fun equalTo(factAp: InitialFactAp): Boolean

    fun hasEmptyDelta(other: InitialFactAp): Boolean =
        delta(other).any { it.isEmpty }

    fun clearAllAccessorOccurrences(accessor: Accessor, keepStartAccessor: Boolean): FinalFactAp?
}

/**
 * [FinalFactAp.Delta.minDepthToAccessor] over the [ReadableAccessorList] interface alone, for
 * representations that have nothing faster to offer.
 *
 * A breadth-first walk, so the first arrival is the shortest one, with the zero-cost `[any]`
 * edges closed into the level before it is stepped: that is a 0-1 BFS, and it keeps the distance
 * exact. A delta is a DAG rather than a tree, so the visited set is what keeps the walk linear
 * in its nodes instead of in its paths.
 */
private fun FinalFactAp.Delta.genericMinDepthToAccessor(accessor: Accessor): Int {
    var depth = 0
    var frontier = mutableListOf(this)
    val visited = hashSetOf<FinalFactAp.Delta>(this)

    while (frontier.isNotEmpty()) {
        // `[any]` consumes nothing, so what is below it sits at the current depth
        var i = 0
        while (i < frontier.size) {
            val anyNode = frontier[i++].readAccessor(AnyAccessor) ?: continue
            if (visited.add(anyNode)) frontier.add(anyNode)
        }

        val next = mutableListOf<FinalFactAp.Delta>()
        for (node in frontier) {
            for (nodeAccessor in node.getStartAccessors()) {
                if (nodeAccessor == AnyAccessor) continue
                if (nodeAccessor == accessor) return depth + 1

                val child = node.readAccessor(nodeAccessor) ?: continue
                if (visited.add(child)) next.add(child)
            }
        }

        depth++
        frontier = next
    }

    return -1
}
