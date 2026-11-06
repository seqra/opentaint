package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrays
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import it.unimi.dsi.fastutil.objects.Object2IntOpenCustomHashMap

/**
 * The node table (IMPL §3.3, spec §4). A node is one origin set, stored as a sorted array of
 * origin ids. The table interns each set one time, so two node ids are equal if and only if their
 * sets are equal. Node [EMPTY_NODE] (0) is the empty set.
 *
 * All states of one method share one table. The fixpoint is single-threaded. After [freeze], the
 * table is read-only: an operation that needs a new node causes [IllegalStateException], and an
 * operation on known nodes does not write a memo.
 */
class NodeTable {
    private val sets = ArrayList<IntArray>()
    private val ids = Object2IntOpenCustomHashMap<IntArray>(IntArrays.HASH_STRATEGY).also { it.defaultReturnValue(NO_ID) }
    private val singletons = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val unionMemo = Long2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val renameMemo = Long2ObjectOpenHashMap<Int2IntOpenHashMap>()
    private var frozen = false

    init {
        val empty = IntArray(0)
        sets.add(empty)
        ids.put(empty, EMPTY_NODE)
    }

    /** The number of nodes, the empty node included. */
    val nodeCount: Int get() = sets.size

    /** The number of memoized unions. */
    val unionMemoSize: Int get() = unionMemo.size

    /** The number of memoized renames. */
    val renameMemoSize: Int get() = renameMemo.values.sumOf { it.size }

    val isFrozen: Boolean get() = frozen

    /** The sorted origin ids of node [n]. The caller must not change the array. */
    fun members(n: NodeId): IntArray = sets[n]

    fun size(n: NodeId): Int = sets[n].size

    fun singleton(o: OriginId): NodeId {
        val known = singletons.get(o)
        if (known != NO_ID) return known
        val n = intern(intArrayOf(o))
        if (!frozen) singletons.put(o, n)
        return n
    }

    /**
     * The node of a sorted array without duplicates. The table keeps the array if the set is new,
     * so the caller must not change it later.
     */
    fun intern(sorted: IntArray): NodeId {
        val known = ids.getInt(sorted)
        if (known != NO_ID) return known
        check(!frozen) { "NodeTable is frozen: no new node" }
        val n = sets.size
        sets.add(sorted)
        ids.put(sorted, n)
        return n
    }

    /** The node of a set of origins in any order, with duplicates allowed. */
    fun of(vararg origins: OriginId): NodeId {
        if (origins.isEmpty()) return EMPTY_NODE
        val sorted = origins.copyOf()
        sorted.sort()
        var size = 1
        for (i in 1 until sorted.size) {
            if (sorted[i] != sorted[size - 1]) sorted[size++] = sorted[i]
        }
        return intern(if (size == sorted.size) sorted else sorted.copyOf(size))
    }

    /** The node of a set, or [NO_ID] if the table has no node for it. */
    fun find(sorted: IntArray): NodeId = ids.getInt(sorted)

    /** The union of two nodes. It is memoized with the key (min, max). */
    fun union(a: NodeId, b: NodeId): NodeId {
        if (a == b || b == EMPTY_NODE) return a
        if (a == EMPTY_NODE) return b
        val key = if (a < b) pairKey(a, b) else pairKey(b, a)
        val known = unionMemo.get(key)
        if (known != NO_ID) return known
        val n = intern(mergeSorted(sets[a], sets[b]))
        if (!frozen) unionMemo.put(key, n)
        return n
    }

    /** True if the set of [a] is a subset of the set of [b]. */
    fun subset(a: NodeId, b: NodeId): Boolean {
        if (a == b || a == EMPTY_NODE) return true
        val x = sets[a]
        val y = sets[b]
        if (x.size > y.size) return false
        var j = 0
        for (o in x) {
            while (j < y.size && y[j] < o) j++
            if (j == y.size || y[j] != o) return false
            j++
        }
        return true
    }

    fun contains(n: NodeId, o: OriginId): Boolean = IntArrays.binarySearch(sets[n], o) >= 0

    /** Node [n] with origin [from] replaced by origin [to]. It is memoized. */
    fun rename(n: NodeId, from: OriginId, to: OriginId): NodeId {
        if (from == to || !contains(n, from)) return n
        val memo = renameMemo.get(pairKey(from, to))
        if (memo != null) {
            val known = memo.get(n)
            if (known != NO_ID) return known
        }
        val src = sets[n]
        val removed = IntArray(src.size - 1)
        var i = 0
        for (o in src) if (o != from) removed[i++] = o
        val result = if (IntArrays.binarySearch(removed, to) >= 0) {
            intern(removed)
        } else {
            intern(mergeSorted(removed, intArrayOf(to)))
        }
        if (!frozen) {
            val m = memo ?: Int2IntOpenHashMap().also {
                it.defaultReturnValue(NO_ID)
                renameMemo.put(pairKey(from, to), it)
            }
            m.put(n, result)
        }
        return result
    }

    fun freeze() {
        frozen = true
    }

    private fun pairKey(a: Int, b: Int): Long = (a.toLong() shl 32) or (b.toLong() and 0xFFFF_FFFFL)

    private fun mergeSorted(x: IntArray, y: IntArray): IntArray {
        val out = IntArray(x.size + y.size)
        var i = 0
        var j = 0
        var k = 0
        while (i < x.size && j < y.size) {
            val a = x[i]
            val b = y[j]
            when {
                a < b -> { out[k++] = a; i++ }
                a > b -> { out[k++] = b; j++ }
                else -> { out[k++] = a; i++; j++ }
            }
        }
        while (i < x.size) out[k++] = x[i++]
        while (j < y.size) out[k++] = y[j++]
        return if (k == out.size) out else out.copyOf(k)
    }
}
