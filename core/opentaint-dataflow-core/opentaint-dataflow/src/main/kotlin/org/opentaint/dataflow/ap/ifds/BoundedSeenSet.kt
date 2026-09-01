package org.opentaint.dataflow.ap.ifds

internal class BoundedSeenSet<T : Any>(
    private val maximumSlotCount: Int = 524_288,
    initialSlotCount: Int = 1_024,
) {
    private var entries = arrayOfNulls<Any>(initialSlotCount)
    private var size = 0

    init {
        require(initialSlotCount > 0 && initialSlotCount.countOneBits() == 1)
        require(maximumSlotCount >= initialSlotCount && maximumSlotCount.countOneBits() == 1)
    }

    @Synchronized
    fun markNew(value: T): Boolean {
        while (true) {
            val location = locate(value)
            if (location < 0) return false
            if (size < retainedLimit(entries.size)) {
                entries[location] = value
                size++
                return true
            }
            if (entries.size == maximumSlotCount) return true
            grow()
        }
    }

    private fun locate(value: T): Int {
        val mask = entries.lastIndex
        val hash = value.hashCode()
        var index = (hash xor (hash ushr 16)) and mask
        while (true) {
            val current = entries[index] ?: return index
            if (current == value) return -index - 1
            index = (index + 1) and mask
        }
    }

    private fun grow() {
        val previous = entries
        entries = arrayOfNulls(previous.size * 2)
        previous.forEach { value ->
            if (value != null) insertRetained(value)
        }
    }

    private fun insertRetained(value: Any) {
        val mask = entries.lastIndex
        val hash = value.hashCode()
        var index = (hash xor (hash ushr 16)) and mask
        while (entries[index] != null) {
            index = (index + 1) and mask
        }
        entries[index] = value
    }

    private fun retainedLimit(slotCount: Int): Int = slotCount * 3 / 4
}
