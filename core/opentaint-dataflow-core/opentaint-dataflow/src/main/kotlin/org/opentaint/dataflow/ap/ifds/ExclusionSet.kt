package org.opentaint.dataflow.ap.ifds

import it.unimi.dsi.fastutil.ints.IntList
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.util.PersistentIntSet

sealed interface ExclusionSet {
    operator fun contains(accessor: AccessorIdx): Boolean
    fun add(accessor: AccessorIdx): ExclusionSet
    fun union(other: ExclusionSet): ExclusionSet
    fun intersect(other: ExclusionSet): ExclusionSet
    fun subtract(accessor: AccessorIdx): ExclusionSet

    fun contains(other: ExclusionSet): Boolean

    data object Empty : ExclusionSet {
        override fun contains(accessor: AccessorIdx): Boolean = false
        override fun add(accessor: AccessorIdx): ExclusionSet = Concrete(accessor)
        override fun union(other: ExclusionSet): ExclusionSet = other
        override fun intersect(other: ExclusionSet): ExclusionSet = this
        override fun subtract(accessor: AccessorIdx): ExclusionSet = this
        override fun contains(other: ExclusionSet): Boolean = other is Empty

        override fun toString(): String = "{}"
    }

    data object Universe : ExclusionSet {
        override fun contains(accessor: AccessorIdx): Boolean = true
        override fun add(accessor: AccessorIdx): ExclusionSet = this
        override fun union(other: ExclusionSet): ExclusionSet = this
        override fun intersect(other: ExclusionSet): ExclusionSet = other
        override fun subtract(accessor: AccessorIdx): ExclusionSet = error("Can't subtract from $this")
        override fun contains(other: ExclusionSet): Boolean = true

        override fun toString(): String = "*"
    }

    data class Concrete(
        val set: PersistentIntSet,
        private val hash: Int,
    ) : ExclusionSet {
        constructor(accessor: AccessorIdx) : this(PersistentIntSet.singleton(accessor), accessor.hashCode())

        override fun hashCode(): Int = hash

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Concrete) return false

            if (hash != other.hash) return false
            return set == other.set
        }

        override fun contains(accessor: AccessorIdx): Boolean = set.contains(accessor)

        override fun add(accessor: AccessorIdx): ExclusionSet {
            val setWithAccessor = set.persistentAdd(accessor)
            if (setWithAccessor === set) return this
            return Concrete(setWithAccessor, hash + accessor.hashCode())
        }

        override fun union(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> this
            Universe -> other
            is Concrete -> {
                val union = set.persistentAddAll(other.set)
                if (union === set) this else Concrete(union, union.hashCode())
            }
        }

        override fun intersect(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> other
            Universe -> this
            is Concrete -> {
                val intersection = set.persistentRetainAll(other.set)
                when {
                    intersection === set -> this
                    intersection.isEmpty() -> Empty
                    else -> Concrete(intersection, intersection.hashCode())
                }
            }
        }

        override fun subtract(accessor: AccessorIdx): ExclusionSet {
            val subtractResult = set.persistentRemove(accessor)
            return when {
                subtractResult === set -> this
                subtractResult.isEmpty() -> Empty
                else -> Concrete(subtractResult, hash - accessor.hashCode())
            }
        }

        override fun contains(other: ExclusionSet): Boolean = when (other) {
            Empty -> true
            Universe -> false
            is Concrete -> set.containsAll(other.set)
        }

        override fun toString(): String = set.joinToString(prefix = "{", postfix = "}") { it.toString() }
    }

    companion object {
        fun create(accessors: IntList): ExclusionSet {
            if (accessors.isEmpty()) return Empty

            val set = PersistentIntSet.create(accessors)
            return Concrete(set, set.hashCode())
        }
    }
}
