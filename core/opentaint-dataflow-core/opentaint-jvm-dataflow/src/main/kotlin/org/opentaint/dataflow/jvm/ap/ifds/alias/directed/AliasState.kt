package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList

/**
 * The alias state at one program point (IMPL §3.4, spec §4).
 *
 * - [env]: `VarId -> NodeId`. An absent key is an unassigned variable (the empty set). `this` and
 *   the arguments are not in `env`: their value is their root by rule. The reserved keys [ETREE]
 *   and [EVAL] are keys of `env`. Absent means the empty set.
 * - [heap]: `HeapKey -> NodeId`. An absent key holds the default content of its cell by rule
 *   ([OriginTable.defaultNode]).
 *
 * Normal form: `heap` has no entry equal to its default node, and `env` has no entry for the empty
 * set. Then two states are equal if and only if their maps are equal (`nf_mapEq_iff`). The
 * operations of [AliasTransfer] keep the normal form.
 *
 * A state does not change after its construction. An operation that changes a map makes a copy
 * (copy on write). An operation that does not change a map shares it. The caller must not change
 * the maps.
 */
class AliasState(val env: Int2IntOpenHashMap, val heap: Long2IntOpenHashMap) {

    init {
        env.defaultReturnValue(EMPTY_NODE)
        heap.defaultReturnValue(NO_ID)
    }

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

    /** The index of the written heap entries. The state computes it at the first use. */
    val index: AliasStateIndex by lazy(LazyThreadSafetyMode.PUBLICATION) { AliasStateIndex(this) }

    fun edit(): Editor = Editor(this)

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
     * Raw changes of a state with copy on write. The editor copies a map at its first change. It
     * does not normalize heap entries: [AliasTransfer.put] does that.
     */
    class Editor(private val base: AliasState) {
        private var env: Int2IntOpenHashMap? = null
        private var heap: Long2IntOpenHashMap? = null

        /** Sets variable [v] to node [n]. The empty node removes the variable. */
        fun setVar(v: VarId, n: NodeId) {
            val current = (env ?: base.env).get(v)
            if (current == n) return
            val m = env ?: copyEnv(base.env).also { env = it }
            if (n == EMPTY_NODE) m.remove(v) else m.put(v, n)
        }

        fun removeVar(v: VarId) = setVar(v, EMPTY_NODE)

        /** Sets heap entry [key] to node [n]. The caller makes sure that [n] is not the default. */
        fun setHeap(key: HeapKey, n: NodeId) {
            if ((heap ?: base.heap).get(key) == n) return
            val m = heap ?: copyHeap(base.heap).also { heap = it }
            m.put(key, n)
        }

        /** Removes heap entry [key]: the cell gets its default content. */
        fun removeHeap(key: HeapKey) {
            if (!(heap ?: base.heap).containsKey(key)) return
            val m = heap ?: copyHeap(base.heap).also { heap = it }
            m.remove(key)
        }

        fun varNode(v: VarId): NodeId = (env ?: base.env).get(v)

        fun heapNode(key: HeapKey): NodeId = (heap ?: base.heap).get(key)

        /** The new state, or the input state if nothing changed. */
        fun build(): AliasState {
            val e = env
            val h = heap
            if (e == null && h == null) return base
            return AliasState(e ?: base.env, h ?: base.heap)
        }
    }

    companion object {
        /**
         * The state with no assigned local and no written cell: the entry state of a method.
         * It is not a bottom element for [AliasTransfer.join]: each cell of it holds its default
         * content. A missing input of a join is no state (`null`), not this state.
         */
        val EMPTY = AliasState(Int2IntOpenHashMap(), Long2IntOpenHashMap())

        internal fun copyEnv(m: Int2IntOpenHashMap): Int2IntOpenHashMap =
            Int2IntOpenHashMap(m).also { it.defaultReturnValue(EMPTY_NODE) }

        internal fun copyHeap(m: Long2IntOpenHashMap): Long2IntOpenHashMap =
            Long2IntOpenHashMap(m).also { it.defaultReturnValue(NO_ID) }
    }
}

/**
 * The index of the written heap entries of one state (IMPL §4.3): the written cells grouped by
 * origin. The retire uses it for the written cells of `AllocNew(s)` and `AllocOld(s)`. The call
 * closure and the query can use it too.
 */
class AliasStateIndex(state: AliasState) {
    private val cellsByOrigin = Int2ObjectOpenHashMap<IntArrayList>()

    /** The written heap keys, in the iteration order of the heap map. */
    val writtenKeys: LongArrayList = LongArrayList(state.heap.size)

    init {
        state.forEachHeap { key, _ ->
            writtenKeys.add(key)
            val o = heapKeyOrigin(key)
            var cells = cellsByOrigin.get(o)
            if (cells == null) {
                cells = IntArrayList(2)
                cellsByOrigin.put(o, cells)
            }
            cells.add(heapKeyCell(key))
        }
    }

    /** The written cells of origin [o]. */
    fun writtenCells(o: OriginId): IntArray = cellsByOrigin.get(o)?.toIntArray() ?: EMPTY_CELLS

    /** The origins with at least one written cell. */
    fun writtenOrigins(): IntArray = cellsByOrigin.keys.toIntArray()

    private companion object {
        val EMPTY_CELLS = IntArray(0)
    }
}
