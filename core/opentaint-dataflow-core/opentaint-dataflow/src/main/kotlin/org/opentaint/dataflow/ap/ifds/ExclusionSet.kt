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

    data object Empty : ExclusionSet {
        override fun contains(accessor: Accessor): Boolean = false
        override fun add(accessor: Accessor): ExclusionSet = Concrete(accessor)
        override fun union(other: ExclusionSet): ExclusionSet = other
        override fun intersect(other: ExclusionSet): ExclusionSet = this
        override fun subtract(accessor: Accessor): ExclusionSet = this
        override fun contains(other: ExclusionSet): Boolean = other is Empty

        override fun toString(): String = "{}"
    }

    data object Universe : ExclusionSet {
        override fun contains(accessor: Accessor): Boolean = true
        override fun add(accessor: Accessor): ExclusionSet = this
        override fun union(other: ExclusionSet): ExclusionSet = this
        override fun intersect(other: ExclusionSet): ExclusionSet = other
        override fun subtract(accessor: Accessor): ExclusionSet = error("Can't subtract from $this")
        override fun contains(other: ExclusionSet): Boolean = true

        override fun toString(): String = "*"
    }

    class Concrete private constructor(
        val set: Set<Accessor>,
        @Volatile
        private var cachedHash: Int?,
    ) : ExclusionSet {
        constructor(set: PersistentSet<Accessor>) : this(set, null)
        constructor(accessor: Accessor) : this(persistentHashSetOf(accessor), accessor.hashCode())
        private constructor(set: Set<Accessor>) : this(set, null)
        internal constructor(set: PersistentAccessorSet) : this(set, set.hashCode())

        override fun hashCode(): Int {
            cachedHash?.let { return it }
            return set.hashCode().also { cachedHash = it }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Concrete) return false

            val currentHash = cachedHash
            val otherHash = other.cachedHash
            if (currentHash != null && otherHash != null && currentHash != otherHash) return false
            return set == other.set
        }

        override fun contains(accessor: Accessor): Boolean = set.contains(accessor)

        override fun add(accessor: Accessor): ExclusionSet {
            val setWithAccessor = set.persistentAdd(accessor)
            if (setWithAccessor === set) return this

            return Concrete(setWithAccessor, hashCode() + accessor.hashCode())
        }

        override fun union(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> this
            Universe -> other
            is Concrete -> {
                val union = set.persistentAddAll(other.set)
                if (union === set) this else Concrete(union)
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
                    else -> Concrete(intersection)
                }
            }
        }

        override fun subtract(accessor: Accessor): ExclusionSet {
            val subtractResult = set.persistentRemove(accessor)
            return when {
                subtractResult === set -> this
                subtractResult.isEmpty() -> Empty
                else -> Concrete(subtractResult, hashCode() - accessor.hashCode())
            }
        }

        internal fun subtract(other: Concrete): ExclusionSet {
            val subtractResult = set.persistentRemoveAll(other.set)
            return when {
                subtractResult === set -> this
                subtractResult.isEmpty() -> Empty
                else -> Concrete(subtractResult)
            }
        }

        override fun contains(other: ExclusionSet): Boolean = when (other) {
            Empty -> true
            Universe -> false
            is Concrete -> set.containsAll(other.set)
        }

        override fun toString(): String = set.joinToString(prefix = "{", postfix = "}") { it.toSuffix() }
    }
}

internal interface PersistentAccessorSet : Set<Accessor> {
    fun addPersistent(accessor: Accessor): PersistentAccessorSet
    fun addAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet
    fun retainAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet
    fun removePersistent(accessor: Accessor): PersistentAccessorSet
    fun removeAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet
}

private fun Set<Accessor>.persistentAdd(accessor: Accessor): Set<Accessor> = when (this) {
    is PersistentAccessorSet -> addPersistent(accessor)
    is PersistentSet<Accessor> -> add(accessor)
    else -> persistentHashSetOf<Accessor>().addAll(this).add(accessor)
}

private fun Set<Accessor>.persistentAddAll(other: Set<Accessor>): Set<Accessor> = when (this) {
    is PersistentAccessorSet -> addAllPersistent(other)
    is PersistentSet<Accessor> -> addAll(other)
    else -> persistentHashSetOf<Accessor>().addAll(this).addAll(other)
}

private fun Set<Accessor>.persistentRetainAll(other: Set<Accessor>): Set<Accessor> = when (this) {
    is PersistentAccessorSet -> retainAllPersistent(other)
    is PersistentSet<Accessor> -> retainAll(other)
    else -> persistentHashSetOf<Accessor>().addAll(this).retainAll(other)
}

private fun Set<Accessor>.persistentRemove(accessor: Accessor): Set<Accessor> = when (this) {
    is PersistentAccessorSet -> removePersistent(accessor)
    is PersistentSet<Accessor> -> remove(accessor)
    else -> persistentHashSetOf<Accessor>().addAll(this).remove(accessor)
}

private fun Set<Accessor>.persistentRemoveAll(other: Set<Accessor>): Set<Accessor> = when (this) {
    is PersistentAccessorSet -> removeAllPersistent(other)
    is PersistentSet<Accessor> -> removeAll(other)
    else -> persistentHashSetOf<Accessor>().addAll(this).removeAll(other)
}
