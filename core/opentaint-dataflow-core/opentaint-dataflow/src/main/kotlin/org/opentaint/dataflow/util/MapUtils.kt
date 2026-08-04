package org.opentaint.dataflow.util

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap

fun <V> int2ObjectMap() = ConcurrentReadSafeInt2ObjectMap<V>()

fun <V : Any> long2ObjectMap() = ConcurrentReadSafeLong2ObjectMap<V>()

fun longSet() = ConcurrentReadSafeLongSet()

inline fun <V> ConcurrentReadSafeInt2ObjectMap<V>.forEachEntry(body: (Int, V) -> Unit) {
    if (isEmpty()) return

    while (true) {
        val containsNullKey = getContainsNullKey()
        val key = getKeys()
        val value = getValues()
        val n = getN()

        // capture arrays to allow concurrent reads
        if (key.size != n + 1 || value.size != n + 1) continue

        if (containsNullKey) {
            body(0, value[n] as V)
        }

        for (i in 0 until n) {
            val k = key[i]
            if (k == 0) continue

            body(k, value[i] as V)
        }

        return
    }
}

inline fun <V : Any> ConcurrentReadSafeLong2ObjectMap<V>.forEachEntry(body: (Long, V) -> Unit) {
    if (isEmpty()) return

    while (true) {
        val containsNullKey = getContainsNullKey()
        val key = getKeys()
        val value = getValues()
        val n = getN()

        // Capture arrays from one table generation to allow a read during rehash.
        if (key.size != n + 1 || value.size != n + 1) continue

        if (containsNullKey) {
            // A writer publishes the key before the value. A concurrent reader may briefly see null.
            value[n]?.let { body(0, it) }
        }

        for (i in 0 until n) {
            val k = key[i]
            if (k == 0L) continue

            // Weak iteration may omit an entry being published, but must never expose a null value.
            value[i]?.let { body(k, it) }
        }

        return
    }
}

inline fun ConcurrentReadSafeLongSet.forEachLong(body: (Long) -> Unit) {
    if (isEmpty()) return

    while (true) {
        val containsNull = getContainsNull()
        val key = getKeys()
        val n = getN()

        // Capture one complete table generation to allow a read during rehash.
        if (key.size != n + 1) continue

        if (containsNull) body(0)

        for (i in 0 until n) {
            val k = key[i]
            if (k != 0L) body(k)
        }

        return
    }
}

inline fun <V> Int2ObjectOpenHashMap<V>.getOrCreate(key: Int, body: () -> V): V {
    get(key)?.let { return it }
    return body().also { put(key, it) }
}

inline fun <V> Int2ObjectOpenHashMap<V?>.getOrCreateNullable(key: Int, body: () -> V): V {
    get(key)?.let { return it }
    return body().also { put(key, it) }
}

inline fun <V> Long2ObjectOpenHashMap<V>.getOrCreate(key: Long, body: () -> V): V {
    get(key)?.let { return it }
    return body().also { put(key, it) }
}

fun <K> object2IntMap() = ConcurrentReadSafeObject2IntMap<K>()

fun <K> ConcurrentReadSafeObject2IntMap<K>.getValue(key: K): Int {
    val value = getInt(key)
    check(value != ConcurrentReadSafeObject2IntMap.NO_VALUE) { "No value for $key found in $this" }
    return value
}

inline fun <K> ConcurrentReadSafeObject2IntMap<K>.getOrCreateIndex(key: K, onNewIndex: (Int) -> Nothing): Int {
    val newIndex = size
    val currentIndex = putIfAbsent(key, newIndex)
    if (currentIndex != ConcurrentReadSafeObject2IntMap.NO_VALUE) return currentIndex
    onNewIndex(newIndex)
}

inline fun <K> ConcurrentReadSafeObject2IntMap<K>.getOrCreateIndexWithEffect(key: K, effect: (Int) -> Unit): Int {
    return getOrCreateIndex(key) {
        effect(it)
        return it
    }
}
