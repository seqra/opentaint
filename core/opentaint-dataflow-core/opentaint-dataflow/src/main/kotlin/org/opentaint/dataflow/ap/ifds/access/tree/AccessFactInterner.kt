package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap

class AccessFactInterner<T : Any>(
    private val maxEntries: Int = 250_000,
) {
    private val cache = Object2ObjectOpenHashMap<T, T>()

    init {
        require(maxEntries > 0)
    }

    @Synchronized
    fun intern(value: T): T {
        cache[value]?.let { return it }
        if (cache.size >= maxEntries) cache.clear()
        cache[value] = value
        return value
    }
}
