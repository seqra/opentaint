package org.opentaint.dataflow.ap.ifds

import kotlinx.collections.immutable.PersistentSet
import kotlinx.collections.immutable.persistentHashSetOf

sealed interface ExclusionSet {
    operator fun contains(accessor: Accessor): Boolean
    fun add(accessor: Accessor): ExclusionSet
    fun union(other: ExclusionSet): ExclusionSet
    fun intersect(other: ExclusionSet): ExclusionSet
    fun subtract(accessor: Accessor): ExclusionSet

    fun contains(other: ExclusionSet): Boolean

    fun mergeAndIntersectDeep(other: ExclusionSet): ExclusionSet
    fun deepExclusion(): Set<DeepMarkExclusion>

    data object Empty : ExclusionSet {
        override fun contains(accessor: Accessor): Boolean = false
        override fun add(accessor: Accessor): ExclusionSet = Concrete(accessor)
        override fun union(other: ExclusionSet): ExclusionSet = other
        override fun intersect(other: ExclusionSet): ExclusionSet = this
        override fun subtract(accessor: Accessor): ExclusionSet = this
        override fun contains(other: ExclusionSet): Boolean = other is Empty

        override fun toString(): String = "{}"

        override fun mergeAndIntersectDeep(other: ExclusionSet): ExclusionSet = when (other) {
            is Empty, is Universe -> other
            is Concrete -> other.mergeAndIntersectDeep(this)
        }

        override fun deepExclusion(): Set<DeepMarkExclusion> = emptySet()
    }

    data object Universe : ExclusionSet {
        override fun contains(accessor: Accessor): Boolean = true
        override fun add(accessor: Accessor): ExclusionSet = this
        override fun union(other: ExclusionSet): ExclusionSet = this
        override fun intersect(other: ExclusionSet): ExclusionSet = other
        override fun subtract(accessor: Accessor): ExclusionSet = error("Can't subtract from $this")
        override fun contains(other: ExclusionSet): Boolean = true

        override fun toString(): String = "*"

        override fun mergeAndIntersectDeep(other: ExclusionSet): ExclusionSet = this
        override fun deepExclusion(): Set<DeepMarkExclusion> = emptySet()
    }

    data class Concrete(
        private val set: PersistentSet<Accessor>,
        private val deepExclusion: PersistentSet<DeepMarkExclusion>,
        private val hash: Int,
    ) : ExclusionSet {
        constructor(accessor: Accessor) : this(
            set = if (accessor !is DeepMarkExclusion) persistentHashSetOf(accessor) else persistentHashSetOf(),
            deepExclusion = if (accessor is DeepMarkExclusion) persistentHashSetOf(accessor) else persistentHashSetOf(),
            accessor.hashCode()
        )

        override fun hashCode(): Int = hash

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Concrete) return false

            if (hash != other.hash) return false
            return set == other.set && deepExclusion == other.deepExclusion
        }

        override fun contains(accessor: Accessor): Boolean =
            if (accessor !is DeepMarkExclusion) {
                set.contains(accessor)
            } else {
                deepExclusion.contains(accessor)
            }

        override fun add(accessor: Accessor): ExclusionSet {
            if (accessor !is DeepMarkExclusion) {
                val setWithAccessor = set.add(accessor)
                if (setWithAccessor === set) return this

                return Concrete(setWithAccessor, deepExclusion, hash + accessor.hashCode())
            } else {
                val setWithAccessor = deepExclusion.add(accessor)
                if (setWithAccessor === deepExclusion) return this

                return Concrete(set, setWithAccessor, hash + accessor.hashCode())
            }
        }

        override fun union(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> this
            Universe -> other
            is Concrete -> {
                check(this.deepExclusion.isEmpty() && other.deepExclusion.isEmpty()) {
                    "Union of deep exclusions is impossible"
                }

                val union = set.addAll(other.set)
                if (union === set) this else Concrete(union, deepExclusion, union.hashCode())
            }
        }

        override fun mergeAndIntersectDeep(other: ExclusionSet): ExclusionSet = when (other) {
            is Universe -> other
            is Empty -> when {
                set.isEmpty() -> Empty
                deepExclusion.isEmpty() -> this
                else -> Concrete(set, persistentHashSetOf(), set.hashCode())
            }

            is Concrete -> {
                val mergedSet = set.addAll(other.set)
                val mergedDeep = deepExclusion.retainAll(other.deepExclusion)
                if (mergedSet === set && mergedDeep === deepExclusion) {
                    this
                } else {
                    Concrete(mergedSet, deepExclusion, mergedSet.hashCode() + mergedDeep.hashCode())
                }
            }
        }

        override fun deepExclusion(): Set<DeepMarkExclusion> = deepExclusion

        override fun intersect(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> other
            Universe -> this
            is Concrete -> {
                val intersection = set.retainAll(other.set)
                val deepIntersection = deepExclusion.retainAll(other.deepExclusion)
                when {
                    intersection === set && deepIntersection === deepExclusion -> this
                    intersection.isEmpty() && deepIntersection.isEmpty() -> Empty
                    else -> Concrete(intersection, deepIntersection, intersection.hashCode() + deepIntersection.hashCode())
                }
            }
        }

        override fun subtract(accessor: Accessor): ExclusionSet {
            if (accessor !is DeepMarkExclusion) {
                val subtractResult = set.remove(accessor)
                return when {
                    subtractResult === set -> this
                    subtractResult.isEmpty() && deepExclusion.isEmpty() -> Empty
                    else -> Concrete(subtractResult, deepExclusion, hash - accessor.hashCode())
                }
            } else {
                val subtractResult = deepExclusion.remove(accessor)
                return when {
                    subtractResult === deepExclusion -> this
                    set.isEmpty() && subtractResult.isEmpty() -> Empty
                    else -> Concrete(set, subtractResult, hash - accessor.hashCode())
                }
            }
        }

        override fun contains(other: ExclusionSet): Boolean = when (other) {
            Empty -> true
            Universe -> false
            is Concrete -> set.containsAll(other.set) && deepExclusion.containsAll(other.deepExclusion)
        }

        override fun toString(): String {
            val setEx = set.joinToString(prefix = "{", postfix = "}") { it.toSuffix() }
            val deepSetEx = deepExclusion.joinToString(prefix = "{", postfix = "}") { it.toSuffix() }
            return if (deepExclusion.isEmpty()) setEx else "$setEx U D$deepSetEx"
        }
    }
}
