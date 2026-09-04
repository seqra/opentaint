package org.opentaint.dataflow.ap.ifds.access.baseonly

import kotlinx.collections.immutable.PersistentMap
import kotlinx.collections.immutable.persistentHashMapOf
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
    private val chunks: PersistentMap<Int, Long>,
    override val size: Int,
    private val cachedHash: Int,
) : AbstractSet<Accessor>(), PersistentAccessorSet {
    override fun contains(element: Accessor): Boolean =
        containsIndex(manager.interner.index(element))

    fun containsIndex(index: Int): Boolean {
        val mask = chunks[index.chunkIndex()] ?: return false
        return mask and index.chunkBit() != 0L
    }

    fun forEachIndex(consume: (Int) -> Unit) {
        chunks.forEach { (chunkIndex, bits) ->
            var remaining = bits
            while (remaining != 0L) {
                val bit = remaining.countTrailingZeroBits()
                consume((chunkIndex shl CHUNK_BITS) + bit)
                remaining = remaining and (remaining - 1)
            }
        }
    }

    fun union(other: BaseOnlyExclusionAccessorSet): BaseOnlyExclusionAccessorSet {
        require(other.manager === manager)
        return unionWithAdded(other)?.union ?: this
    }

    fun unionIfChanged(other: BaseOnlyExclusionAccessorSet): BaseOnlyExclusionAccessorSet? {
        require(other.manager === manager)
        return unionWithAdded(other)?.union
    }

    /**
     * Adds [other] and returns both the union and the elements that [other] added.
     * The unchanged case performs no allocation, which is important for repeated
     * side-effect requirements.
     */
    fun unionWithAdded(other: BaseOnlyExclusionAccessorSet): UnionWithAdded? {
        require(other.manager === manager)
        if (other.isEmpty()) return null

        var unionChunks = chunks
        var addedChunks = persistentHashMapOf<Int, Long>()
        var addedSize = 0
        var addedHash = 0
        other.chunks.forEach { (chunkIndex, otherBits) ->
            val currentBits = chunks[chunkIndex] ?: 0L
            val newBits = otherBits and currentBits.inv()
            if (newBits == 0L) return@forEach

            unionChunks = unionChunks.put(chunkIndex, currentBits or newBits)
            addedChunks = addedChunks.put(chunkIndex, newBits)
            var remaining = newBits
            while (remaining != 0L) {
                val bit = remaining.countTrailingZeroBits()
                addedSize++
                addedHash += accessorHash((chunkIndex shl CHUNK_BITS) + bit)
                remaining = remaining and (remaining - 1)
            }
        }
        if (addedSize == 0) return null

        return UnionWithAdded(
            union = BaseOnlyExclusionAccessorSet(manager, unionChunks, size + addedSize, cachedHash + addedHash),
            added = BaseOnlyExclusionAccessorSet(manager, addedChunks, addedSize, addedHash),
        )
    }

    override fun iterator(): Iterator<Accessor> = object : Iterator<Accessor> {
        private val chunkIterator = chunks.entries.sortedBy { it.key }.iterator()
        private var chunkIndex = 0
        private var remaining = 0L

        init {
            advanceChunk()
        }

        override fun hasNext(): Boolean = remaining != 0L

        override fun next(): Accessor {
            if (!hasNext()) throw NoSuchElementException()
            val bit = remaining.countTrailingZeroBits()
            val index = (chunkIndex shl CHUNK_BITS) + bit
            remaining = remaining and (remaining - 1)
            if (remaining == 0L) advanceChunk()
            return manager.interner.accessor(index)
                ?: error("Accessor not found")
        }

        private fun advanceChunk() {
            if (!chunkIterator.hasNext()) return
            val entry = chunkIterator.next()
            chunkIndex = entry.key
            remaining = entry.value
        }
    }

    override fun hashCode(): Int = cachedHash

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other is BaseOnlyExclusionAccessorSet) {
            return manager === other.manager &&
                size == other.size && cachedHash == other.cachedHash && chunks == other.chunks
        }
        return super.equals(other)
    }

    override fun addPersistent(accessor: Accessor): PersistentAccessorSet {
        val idx = manager.interner.index(accessor)
        if (containsIndex(idx)) return this
        val chunkIndex = idx.chunkIndex()
        val result = chunks.put(chunkIndex, (chunks[chunkIndex] ?: 0L) or idx.chunkBit())
        return BaseOnlyExclusionAccessorSet(manager, result, size + 1, cachedHash + accessor.hashCode())
    }

    override fun addAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet =
        combine(accessors, SetOperation.Union)

    override fun retainAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet =
        combine(accessors, SetOperation.Intersection)

    override fun removePersistent(accessor: Accessor): PersistentAccessorSet {
        val idx = manager.interner.index(accessor)
        val chunkIndex = idx.chunkIndex()
        val currentBits = chunks[chunkIndex] ?: return this
        val bit = idx.chunkBit()
        if (currentBits and bit == 0L) return this
        if (size == 1) return empty(manager)

        val newBits = currentBits and bit.inv()
        val result = if (newBits == 0L) chunks.remove(chunkIndex) else chunks.put(chunkIndex, newBits)
        return BaseOnlyExclusionAccessorSet(manager, result, size - 1, cachedHash - accessor.hashCode())
    }

    override fun removeAllPersistent(accessors: Set<Accessor>): PersistentAccessorSet =
        combine(accessors, SetOperation.Difference)

    private fun combine(
        accessors: Set<Accessor>,
        operation: SetOperation,
    ): BaseOnlyExclusionAccessorSet {
        val other = from(manager, accessors)
        return when (operation) {
            SetOperation.Union -> union(other)
            SetOperation.Intersection -> filterIndices { other.containsIndex(it) }
            SetOperation.Difference -> filterIndices { !other.containsIndex(it) }
        }
    }

    private inline fun filterIndices(crossinline keep: (Int) -> Boolean): BaseOnlyExclusionAccessorSet {
        var resultChunks = persistentHashMapOf<Int, Long>()
        var resultSize = 0
        var resultHash = 0
        forEachIndex { index ->
            if (!keep(index)) return@forEachIndex
            val chunkIndex = index.chunkIndex()
            resultChunks = resultChunks.put(chunkIndex, (resultChunks[chunkIndex] ?: 0L) or index.chunkBit())
            resultSize++
            resultHash += accessorHash(index)
        }
        return when (resultSize) {
            size -> this
            0 -> empty(manager)
            else -> BaseOnlyExclusionAccessorSet(manager, resultChunks, resultSize, resultHash)
        }
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

            var chunks = persistentHashMapOf<Int, Long>()
            var size = 0
            var hash = 0
            accessors.forEach { accessor ->
                val index = manager.interner.index(accessor)
                val chunkIndex = index.chunkIndex()
                val bit = index.chunkBit()
                val currentBits = chunks[chunkIndex] ?: 0L
                if (currentBits and bit != 0L) return@forEach
                chunks = chunks.put(chunkIndex, currentBits or bit)
                size++
                hash += accessor.hashCode()
            }
            return BaseOnlyExclusionAccessorSet(manager, chunks, size, hash)
        }

        fun empty(manager: BaseOnlyApManager): BaseOnlyExclusionAccessorSet =
            BaseOnlyExclusionAccessorSet(manager, persistentHashMapOf(), 0, 0)

        private const val CHUNK_BITS = 6

        private fun Int.chunkIndex(): Int = this ushr CHUNK_BITS
        private fun Int.chunkBit(): Long = 1L shl (this and 63)
    }

    data class UnionWithAdded(
        val union: BaseOnlyExclusionAccessorSet,
        val added: BaseOnlyExclusionAccessorSet,
    )
}
