package org.opentaint.dataflow.util

import java.util.BitSet

class CompactIntSet {
    private var base: Int = 0
    private var offsets: Any? = null

    val size: Int
        get() = when (offsets) {
            null -> 0
            Singleton -> 1
            else -> (offsets as BitSet).cardinality()
        }

    fun clone(): CompactIntSet = CompactIntSet().also { copy ->
        copy.base = base
        copy.offsets = when (offsets) {
            null -> null
            Singleton -> Singleton
            else -> (offsets as BitSet).clone()
        }
    }

    fun contains(element: Int): Boolean {
        val offsets = this.offsets ?: return false
        if (offsets !is BitSet) return element == base

        val offset = element - base
        if (offset < 0) return false
        return offsets.get(offset)
    }

    fun remove(element: Int) {
        val offsets = this.offsets ?: return
        if (offsets !is BitSet) {
            if (element == base) {
                this.offsets = null
            }
            return
        }

        val offset = element - base
        if (offset < 0) return
        offsets.clear(offset)
    }

    fun add(element: Int) {
        var offsets = this.offsets

        if (offsets == null) {
            base = element
            this.offsets = Singleton
            return
        }

        if (element == base) return

        if (offsets !is BitSet) {
            offsets = BitSet()
            offsets.set(0)
            this.offsets = offsets
        }

        val base = this.base

        val offset = element - base
        if (offset >= 0) {
            offsets.set(offset)
            return
        }

        val newBase = element
        val newOffsets = BitSet()
        newOffsets.set(0)

        val oldBaseOffset = -offset
        offsets.forEach { newOffsets.set(oldBaseOffset + it) }

        this.offsets = newOffsets
        this.base = newBase
    }

    fun addAll(other: CompactIntSet) {
        if (this === other) return

        val otherOffsets = other.offsets ?: return
        val thisOffsets = this.offsets
        if (thisOffsets == null) {
            this.base = other.base
            this.offsets = if (otherOffsets !is BitSet) {
                otherOffsets
            } else {
                otherOffsets.clone() as BitSet
            }
            return
        }

        if (otherOffsets !is BitSet) {
            add(other.base)
            return
        }

        if (thisOffsets is BitSet) {
            if (this.base == other.base) {
                thisOffsets.or(otherOffsets)
                return
            }
        }

        other.forEach { add(it) }
    }

    fun base(): Int = base
    fun offset(): Any? = offsets

    inline fun forEach(body: (Int) -> Unit) {
        val offsets = offset() ?: return
        val base = base()

        if (offsets !is BitSet) {
            body(base)
            return
        }

        offsets.forEach { offset -> body(base + offset) }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is CompactIntSet) return false

        if (base != other.base) return false
        if (offsets != other.offsets) return false

        return true
    }

    override fun hashCode(): Int {
        var result = base
        result = 31 * result + (offsets?.hashCode() ?: 0)
        return result
    }

    fun toSet(): Set<Int> {
        val elements = hashSetOf<Int>()
        forEach { elements.add(it) }
        return elements
    }

    override fun toString(): String = toSet().toString()

    companion object {
        private data object Singleton
    }
}
