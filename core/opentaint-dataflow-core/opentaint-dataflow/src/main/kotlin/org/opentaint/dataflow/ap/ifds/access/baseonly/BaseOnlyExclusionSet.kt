package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.PersistentAccessorSet

internal fun BaseOnlyApManager.compactExclusions(exclusions: ExclusionSet): ExclusionSet =
    when (exclusions) {
        ExclusionSet.Empty, ExclusionSet.Universe -> exclusions
        is ExclusionSet.Concrete -> {
            val set = exclusions.set
            if (set is BaseOnlyExclusionAccessorSet && set.manager === this) {
                exclusions
            } else {
                ExclusionSet.Concrete(BaseOnlyExclusionAccessorSet.from(this, set))
            }
        }
    }

internal class BaseOnlyExclusionAccessorSet private constructor(
    val manager: BaseOnlyApManager,
    private val indices: IntArray,
    private val cachedHash: Int,
) : AbstractSet<Accessor>(), PersistentAccessorSet {
    override val size: Int get() = indices.size

    override fun contains(element: Accessor): Boolean =
        indices.binarySearch(manager.interner.index(element)) >= 0

    fun containsIndex(index: Int): Boolean = indices.binarySearch(index) >= 0

    fun forEachIndex(consume: (Int) -> Unit) {
        indices.forEach(consume)
    }

    fun union(other: BaseOnlyExclusionAccessorSet): BaseOnlyExclusionAccessorSet {
        require(other.manager === manager)
        return combine(other, SetOperation.Union)
    }

    /**
     * Adds [other] and returns both the union and the elements that [other] added.
     * The unchanged case performs no allocation, which is important for repeated
     * side-effect requirements.
     */
    fun unionWithAdded(other: BaseOnlyExclusionAccessorSet): UnionWithAdded? {
        require(other.manager === manager)
        if (other.indices.isEmpty()) return null

        var left = 0
        var added: IntArray? = null
        var addedSize = 0
        var addedHash = 0
        for (rightValue in other.indices) {
            while (left < indices.size && indices[left] < rightValue) left++
            if (left < indices.size && indices[left] == rightValue) continue

            val addedIndices = added ?: IntArray(other.indices.size).also { added = it }
            addedIndices[addedSize++] = rightValue
            addedHash += other.accessorHash(rightValue)
        }
        val addedIndices = added?.copyOf(addedSize) ?: return null

        val unionIndices = IntArray(indices.size + addedSize)
        left = 0
        var newElement = 0
        var output = 0
        while (left < indices.size || newElement < addedIndices.size) {
            if (newElement == addedIndices.size ||
                left < indices.size && indices[left] < addedIndices[newElement]
            ) {
                unionIndices[output++] = indices[left++]
            } else {
                unionIndices[output++] = addedIndices[newElement++]
            }
        }

        return UnionWithAdded(
            union = BaseOnlyExclusionAccessorSet(manager, unionIndices, cachedHash + addedHash),
            added = BaseOnlyExclusionAccessorSet(manager, addedIndices, addedHash),
        )
    }

    override fun iterator(): Iterator<Accessor> = object : Iterator<Accessor> {
        private var next = 0

        override fun hasNext(): Boolean = next < indices.size

        override fun next(): Accessor {
            if (!hasNext()) throw NoSuchElementException()
            return manager.interner.accessor(indices[next++])
                ?: error("Accessor not found")
        }
    }

    override fun hashCode(): Int = cachedHash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other is BaseOnlyExclusionAccessorSet) {
            return manager === other.manager && indices.contentEquals(other.indices)
        }
        return super.equals(other)
    }

    override fun addPersistent(accessor: Accessor): PersistentAccessorSet {
        val idx = manager.interner.index(accessor)
        val position = indices.binarySearch(idx)
        if (position >= 0) return this

        val insertionPoint = -position - 1
        val result = IntArray(indices.size + 1)
        indices.copyInto(result, endIndex = insertionPoint)
        result[insertionPoint] = idx
        indices.copyInto(result, destinationOffset = insertionPoint + 1, startIndex = insertionPoint)
        return BaseOnlyExclusionAccessorSet(manager, result, cachedHash + accessor.hashCode())
    }

    override fun addAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet =
        combine(accessors, SetOperation.Union)

    override fun retainAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet =
        combine(accessors, SetOperation.Intersection)

    override fun removePersistent(accessor: Accessor): PersistentAccessorSet {
        val idx = manager.interner.index(accessor)
        val position = indices.binarySearch(idx)
        if (position < 0) return this
        if (indices.size == 1) return empty(manager)

        val result = IntArray(indices.size - 1)
        indices.copyInto(result, endIndex = position)
        indices.copyInto(result, destinationOffset = position, startIndex = position + 1)
        return BaseOnlyExclusionAccessorSet(manager, result, cachedHash - accessor.hashCode())
    }

    override fun removeAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet =
        combine(accessors, SetOperation.Difference)

    private fun combine(
        accessors: Set<Accessor>,
        operation: SetOperation,
    ): BaseOnlyExclusionAccessorSet {
        if (accessors.isEmpty()) {
            return if (operation == SetOperation.Intersection) empty(manager) else this
        }

        val other = from(manager, accessors)
        if (other.indices.isEmpty()) {
            return if (operation == SetOperation.Intersection) empty(manager) else this
        }

        val resultSize = when (operation) {
            SetOperation.Union -> indices.size + other.indices.size
            SetOperation.Intersection -> minOf(indices.size, other.indices.size)
            SetOperation.Difference -> indices.size
        }
        val result = IntArray(resultSize)
        var left = 0
        var right = 0
        var output = 0
        var hash = cachedHash

        while (left < indices.size || right < other.indices.size) {
            val leftValue = indices.getOrNull(left)
            val rightValue = other.indices.getOrNull(right)
            when {
                rightValue == null || leftValue != null && leftValue < rightValue -> {
                    val idx = checkNotNull(leftValue)
                    if (operation == SetOperation.Intersection) {
                        hash -= accessorHash(idx)
                    } else {
                        result[output++] = idx
                    }
                    left++
                }

                leftValue == null || rightValue < leftValue -> {
                    if (operation == SetOperation.Union) {
                        result[output++] = rightValue
                        hash += accessorHash(rightValue)
                    }
                    right++
                }

                else -> {
                    val idx = checkNotNull(leftValue)
                    if (operation == SetOperation.Difference) {
                        hash -= accessorHash(idx)
                    } else {
                        result[output++] = idx
                    }
                    left++
                    right++
                }
            }
        }

        if (output == indices.size && indices.indices.all { result[it] == indices[it] }) return this
        if (output == 0) return empty(manager)
        return BaseOnlyExclusionAccessorSet(manager, result.copyOf(output), hash)
    }

    private fun accessorHash(index: Int): Int =
        manager.interner.accessor(index)?.hashCode() ?: error("Accessor not found: $index")

    private enum class SetOperation {
        Union,
        Intersection,
        Difference,
    }

    companion object {
        fun from(manager: BaseOnlyApManager, accessors: Set<Accessor>): BaseOnlyExclusionAccessorSet {
            if (accessors is BaseOnlyExclusionAccessorSet && accessors.manager === manager) return accessors

            val indices = IntArray(accessors.size)
            var next = 0
            var hash = 0
            accessors.forEach { accessor ->
                indices[next++] = manager.interner.index(accessor)
                hash += accessor.hashCode()
            }
            indices.sort()
            return BaseOnlyExclusionAccessorSet(manager, indices, hash)
        }

        fun empty(manager: BaseOnlyApManager): BaseOnlyExclusionAccessorSet =
            BaseOnlyExclusionAccessorSet(manager, IntArray(0), 0)
    }

    data class UnionWithAdded(
        val union: BaseOnlyExclusionAccessorSet,
        val added: BaseOnlyExclusionAccessorSet,
    )
}
