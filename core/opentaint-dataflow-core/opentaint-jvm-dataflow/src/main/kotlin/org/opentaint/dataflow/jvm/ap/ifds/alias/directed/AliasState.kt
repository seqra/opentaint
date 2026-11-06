package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap

/**
 * The alias state at one program point (IMPL §3.4, spec §4).
 *
 * - [env]: `VarId -> NodeId`. An absent key is an unassigned variable (the empty set). `this` and
 *   the arguments are not in `env`: their value is their root by rule. The reserved keys [ETREE]
 *   and [EVAL] are keys of `env`. Absent means the empty set.
 * - [heap]: `HeapKey -> NodeId`. An absent key holds the default content of its cell by rule
 *   ([OriginTable.defaultNode]).
 * - [index]: the two indexes of IMPL §4.3 ([AliasIndex]). It is derived from the maps.
 *
 * Normal form: `heap` has no entry equal to its default node, and `env` has no entry for the empty
 * set. Then two states are equal if and only if their maps are equal (`nf_mapEq_iff`). The
 * operations of [AliasTransfer] keep the normal form. Equality does not compare the index.
 *
 * A state does not change after its construction. An operation that changes a map or an index
 * makes a copy (copy on write). An operation that does not change it shares it. Only an [Editor]
 * makes a new state, so the index always agrees with the maps.
 */
class AliasState private constructor(
    val env: Int2IntOpenHashMap,
    val heap: Long2IntOpenHashMap,
    val index: AliasIndex,
) {

    /** The node of variable [v], or [EMPTY_NODE] if it is absent. */
    fun varNode(v: VarId): NodeId = env.get(v)

    /** The node of a written heap entry, or [NO_ID] if the entry is absent (default content). */
    fun heapNode(key: HeapKey): NodeId = heap.get(key)

    fun isWritten(key: HeapKey): Boolean = heap.containsKey(key)

    /** Calls [body] for each env entry, [ETREE] and [EVAL] included. */
    inline fun forEachVar(body: (VarId, NodeId) -> Unit) {
        val it = env.int2IntEntrySet().fastIterator()
        while (it.hasNext()) {
            val e = it.next()
            body(e.intKey, e.intValue)
        }
    }

    /** Calls [body] for each written heap entry. */
    inline fun forEachHeap(body: (HeapKey, NodeId) -> Unit) {
        val it = heap.long2IntEntrySet().fastIterator()
        while (it.hasNext()) {
            val e = it.next()
            body(e.longKey, e.intValue)
        }
    }

    /** An editor of this state. [tracker] tells which origins the holders index tracks. */
    fun edit(tracker: LoopAllocTracker): Editor = Editor(this, tracker)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is AliasState) return false
        return env == other.env && heap == other.heap
    }

    override fun hashCode(): Int = 31 * env.hashCode() + heap.hashCode()

    override fun toString(): String = "AliasState(env=$env, heap=${heap.long2IntEntrySet().joinToString(prefix = "{", postfix = "}") {
        "(${heapKeyOrigin(it.longKey)}, ${heapKeyCell(it.longKey)})=${it.intValue}"
    }})"

    /**
     * Raw changes of a state with copy on write. The editor copies a map or an index map at its
     * first change, and it updates the index with each change. It does not normalize heap
     * entries: [AliasTransfer.put] does that.
     */
    class Editor(private val base: AliasState, private val tracker: LoopAllocTracker) {
        private var env: Int2IntOpenHashMap? = null
        private var heap: Long2IntOpenHashMap? = null
        private var cells: Int2ObjectOpenHashMap<IntArray>? = null
        private var holders: Int2ObjectOpenHashMap<AliasIndex.Holders>? = null

        /** Sets variable [v] to node [n]. The empty node removes the variable. */
        fun setVar(v: VarId, n: NodeId) {
            val current = (env ?: base.env).get(v)
            if (current == n) return
            val m = env ?: copyEnv(base.env).also { env = it }
            if (n == EMPTY_NODE) m.remove(v) else m.put(v, n)
            updateHolders(current, n, { h, o -> h.withVar(o) }, { h, o -> h.withoutVar(o) }, v.toLong())
        }

        fun removeVar(v: VarId) = setVar(v, EMPTY_NODE)

        /** Sets heap entry [key] to node [n]. The caller makes sure that [n] is not the default. */
        fun setHeap(key: HeapKey, n: NodeId) {
            val current = (heap ?: base.heap).get(key)
            if (current == n) return
            val m = heap ?: copyHeap(base.heap).also { heap = it }
            m.put(key, n)
            if (current == NO_ID) addCell(key)
            updateHolders(current, n, { h, k -> h.withKey(k) }, { h, k -> h.withoutKey(k) }, key)
        }

        /** Removes heap entry [key]: the cell gets its default content. */
        fun removeHeap(key: HeapKey) {
            val current = (heap ?: base.heap).get(key)
            if (current == NO_ID) return
            val m = heap ?: copyHeap(base.heap).also { heap = it }
            m.remove(key)
            removeCell(key)
            updateHolders(current, NO_ID, { h, k -> h.withKey(k) }, { h, k -> h.withoutKey(k) }, key)
        }

        fun varNode(v: VarId): NodeId = (env ?: base.env).get(v)

        fun heapNode(key: HeapKey): NodeId = (heap ?: base.heap).get(key)

        /** The written cells of [o] in the edited state. */
        fun writtenCells(o: OriginId): IntArray = (cells ?: base.index.cells).get(o) ?: EMPTY_INTS

        /** The holders of a tracked origin [o] in the edited state. */
        fun holders(o: OriginId): AliasIndex.Holders = (holders ?: base.index.holders).get(o) ?: AliasIndex.Holders.NONE

        /** The new state, or the input state if nothing changed. */
        fun build(): AliasState {
            val e = env
            val h = heap
            if (e == null && h == null) return base
            val c = cells
            val hl = holders
            val index = if (c == null && hl == null) {
                base.index
            } else {
                AliasIndex(c ?: base.index.cells, hl ?: base.index.holders)
            }
            return AliasState(e ?: base.env, h ?: base.heap, index)
        }

        private fun cellsForWrite(): Int2ObjectOpenHashMap<IntArray> =
            cells ?: Int2ObjectOpenHashMap(base.index.cells).also { cells = it }

        private fun holdersForWrite(): Int2ObjectOpenHashMap<AliasIndex.Holders> =
            holders ?: Int2ObjectOpenHashMap(base.index.holders).also { holders = it }

        private fun addCell(key: HeapKey) {
            val o = heapKeyOrigin(key)
            val m = cellsForWrite()
            m.put(o, insertSorted(m.get(o) ?: EMPTY_INTS, heapKeyCell(key)))
        }

        private fun removeCell(key: HeapKey) {
            val o = heapKeyOrigin(key)
            val m = cellsForWrite()
            val rest = removeSorted(m.get(o) ?: EMPTY_INTS, heapKeyCell(key))
            if (rest.isEmpty()) m.remove(o) else m.put(o, rest)
        }

        private inline fun updateHolders(
            oldNode: NodeId,
            newNode: NodeId,
            add: (AliasIndex.Holders, Long) -> AliasIndex.Holders,
            remove: (AliasIndex.Holders, Long) -> AliasIndex.Holders,
            holder: Long,
        ) {
            val before = tracker.tracked(oldNode)
            val after = tracker.tracked(newNode)
            if (before.isEmpty() && after.isEmpty()) return
            for (o in before) {
                if (after.binarySearch(o) >= 0) continue
                val m = holdersForWrite()
                val rest = remove(m.get(o) ?: AliasIndex.Holders.NONE, holder)
                if (rest.isEmpty()) m.remove(o) else m.put(o, rest)
            }
            for (o in after) {
                if (before.binarySearch(o) >= 0) continue
                val m = holdersForWrite()
                m.put(o, add(m.get(o) ?: AliasIndex.Holders.NONE, holder))
            }
        }
    }

    companion object {
        /**
         * The state with no assigned local and no written cell: the entry state of a method.
         * It is not a bottom element for [AliasTransfer.join]: each cell of it holds its default
         * content. A missing input of a join is no state (`null`), not this state.
         */
        val EMPTY = AliasState(
            Int2IntOpenHashMap().also { it.defaultReturnValue(EMPTY_NODE) },
            Long2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) },
            AliasIndex.EMPTY,
        )

        private val EMPTY_INTS = IntArray(0)

        private fun copyEnv(m: Int2IntOpenHashMap): Int2IntOpenHashMap =
            Int2IntOpenHashMap(m).also { it.defaultReturnValue(EMPTY_NODE) }

        private fun copyHeap(m: Long2IntOpenHashMap): Long2IntOpenHashMap =
            Long2IntOpenHashMap(m).also { it.defaultReturnValue(NO_ID) }

        private fun insertSorted(a: IntArray, x: Int): IntArray {
            val pos = a.binarySearch(x)
            if (pos >= 0) return a
            val i = -pos - 1
            val r = IntArray(a.size + 1)
            System.arraycopy(a, 0, r, 0, i)
            r[i] = x
            System.arraycopy(a, i, r, i + 1, a.size - i)
            return r
        }

        private fun removeSorted(a: IntArray, x: Int): IntArray {
            val i = a.binarySearch(x)
            if (i < 0) return a
            val r = IntArray(a.size - 1)
            System.arraycopy(a, 0, r, 0, i)
            System.arraycopy(a, i + 1, r, i, a.size - i - 1)
            return r
        }
    }
}

/**
 * The two indexes of one state (IMPL §4.3):
 * - the written cells grouped by origin (`origin -> sorted cells`);
 * - the holders of each tracked origin: `AllocNew(s)` of a loop site `s` (`origin -> env keys and
 *   heap keys whose node holds it`). [LoopAllocTracker] tells which origins are tracked.
 *
 * The index is persistent. The maps and the arrays do not change after construction. An edit that
 * does not change the written key set or a holder set shares the index of its input. An edit that
 * changes them copies the changed map one time (shallow: the arrays are shared) and replaces the
 * changed arrays. So the cost of an edit is at most the size of the copied map, and the editor
 * copies the heap map in the same edit anyway. A state that shares the index of its input costs
 * one reference.
 */
class AliasIndex internal constructor(
    internal val cells: Int2ObjectOpenHashMap<IntArray>,
    internal val holders: Int2ObjectOpenHashMap<Holders>,
) {
    /** The env keys and the heap keys whose node holds one tracked origin. Sorted arrays. */
    class Holders(val vars: IntArray, val keys: LongArray) {
        fun isEmpty(): Boolean = vars.isEmpty() && keys.isEmpty()

        internal fun withVar(v: Long): Holders = Holders(insert(vars, v.toInt()), keys)
        internal fun withoutVar(v: Long): Holders = Holders(remove(vars, v.toInt()), keys)
        internal fun withKey(k: Long): Holders = Holders(vars, insert(keys, k))
        internal fun withoutKey(k: Long): Holders = Holders(vars, remove(keys, k))

        companion object {
            val NONE = Holders(IntArray(0), LongArray(0))

            private fun insert(a: IntArray, x: Int): IntArray {
                val pos = a.binarySearch(x)
                if (pos >= 0) return a
                val i = -pos - 1
                return IntArray(a.size + 1) { j -> if (j < i) a[j] else if (j == i) x else a[j - 1] }
            }

            private fun remove(a: IntArray, x: Int): IntArray {
                val i = a.binarySearch(x)
                if (i < 0) return a
                return IntArray(a.size - 1) { j -> if (j < i) a[j] else a[j + 1] }
            }

            private fun insert(a: LongArray, x: Long): LongArray {
                val pos = a.binarySearch(x)
                if (pos >= 0) return a
                val i = -pos - 1
                return LongArray(a.size + 1) { j -> if (j < i) a[j] else if (j == i) x else a[j - 1] }
            }

            private fun remove(a: LongArray, x: Long): LongArray {
                val i = a.binarySearch(x)
                if (i < 0) return a
                return LongArray(a.size - 1) { j -> if (j < i) a[j] else a[j + 1] }
            }
        }
    }

    /** The written cells of origin [o], sorted. The caller must not change the array. */
    fun writtenCells(o: OriginId): IntArray = cells.get(o) ?: NO_CELLS

    /** The origins with at least one written cell. */
    fun writtenOrigins(): IntArray = cells.keys.toIntArray()

    /** The holders of a tracked origin [o]: `AllocNew(s)` of a loop site `s`. */
    fun holders(o: OriginId): Holders = holders.get(o) ?: Holders.NONE

    /** The tracked origins with at least one holder. */
    fun heldOrigins(): IntArray = holders.keys.toIntArray()

    companion object {
        private val NO_CELLS = IntArray(0)
        val EMPTY = AliasIndex(Int2ObjectOpenHashMap(), Int2ObjectOpenHashMap())
    }
}

/**
 * Tells which origins of a node the holders index tracks: `AllocNew(s)` of a loop site `s`. Only a
 * loop site retires, so only these origins are renamed (IMPL §4.3).
 *
 * The result is cached for each node. So a site must be a loop site before its `AllocNew` origin
 * exists: [SiteTable.markLoopSite] checks this.
 */
class LoopAllocTracker(
    private val nodes: NodeTable,
    private val origins: OriginTable,
    private val sites: SiteTable,
) {
    private val cache = Int2ObjectOpenHashMap<IntArray>()

    /** The tracked origins of node [n], sorted. [NO_ID] and [EMPTY_NODE] give none. */
    fun tracked(n: NodeId): IntArray {
        if (n == NO_ID || n == EMPTY_NODE) return NONE
        val known = cache.get(n)
        if (known != null) return known
        var out: IntArrayList? = null
        for (o in nodes.members(n)) {
            if (origins.isAllocNew(o) && sites.isLoopSite(origins.site(o))) {
                (out ?: IntArrayList(1).also { out = it }).add(o)
            }
        }
        val r = out?.toIntArray() ?: NONE
        if (!nodes.isFrozen) cache.put(n, r)
        return r
    }

    private companion object {
        val NONE = IntArray(0)
    }
}
