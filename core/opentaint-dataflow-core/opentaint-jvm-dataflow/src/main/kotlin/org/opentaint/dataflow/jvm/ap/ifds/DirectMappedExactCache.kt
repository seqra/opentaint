package org.opentaint.dataflow.jvm.ap.ifds

import java.util.concurrent.atomic.AtomicReferenceArray

internal class DirectMappedExactCache<K : Any, V : Any>(slotCount: Int) {
    private data class Entry<K, V>(val key: K, val value: V)

    private val mask = slotCount - 1
    private val entries = AtomicReferenceArray<Entry<K, V>>(slotCount)

    init {
        require(slotCount > 0 && slotCount.countOneBits() == 1)
    }

    fun getOrCompute(key: K, compute: (K) -> V): V {
        val slot = key.hashCode() and mask
        val current = entries.get(slot)
        if (current?.key == key) return current.value

        return compute(key).also { entries.set(slot, Entry(key, it)) }
    }

    internal fun slotCount(): Int = entries.length()
}
