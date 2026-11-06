package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap

/** The key of an origin (IMPL §3.2). */
sealed interface OriginKey {
    /**
     * The value at a path below [base]. [parent] is the origin of the path without its last cell,
     * and [cell] is the last cell. For the base value itself, [parent] and [cell] are [NO_ID].
     */
    data class Sym(val base: BaseId, val parent: OriginId, val cell: CellId) : OriginKey

    /** All values deeper than K below [base]. */
    data class Deep(val base: BaseId) : OriginKey

    /** The most recent object of the allocation site [site]. */
    data class AllocNew(val site: SiteId) : OriginKey

    /** All older objects of the allocation site [site]. */
    data class AllocOld(val site: SiteId) : OriginKey

    /** The marker [OriginTable.REACHED_STATICS]. It is only in `Etree` and `Eval`. */
    data object ReachedStatics : OriginKey

    /** The marker [OriginTable.REACHED_ALL]. It is only in `Etree` and `Eval`. */
    data object ReachedAll : OriginKey
}

/**
 * The origins (IMPL §3.2). A `Sym` origin stores its base, its parent and its last cell. So a path
 * is a parent chain of at most K = [symDepth] steps. A path longer than K gives `Deep(base)`.
 *
 * The ids 0 and 1 are the markers [REACHED_STATICS] and [REACHED_ALL].
 *
 * [defaultNode] gives the default content of a cell by rule. It is cached for each heap key.
 */
class OriginTable(
    val symDepth: Int,
    private val bases: BaseTable,
    private val nodes: NodeTable,
    private val sites: SiteTable,
) {
    private val kinds = IntArrayList()
    private val payloads = IntArrayList() // the base of Sym and Deep, the site of AllocNew and AllocOld
    private val parents = IntArrayList()
    private val cells = IntArrayList()
    private val depths = IntArrayList()
    private val elemFlags = IntArrayList() // 1 if the path has ELEM_CELL

    private val roots = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val children = Long2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val deeps = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val allocNews = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val allocOlds = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private val defaults = Long2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
    private var frozen = false

    init {
        require(symDepth >= 0) { "symDepth must not be negative: $symDepth" }
        check(add(MARKER, NO_ID, NO_ID, NO_ID, NO_ID, 0) == REACHED_STATICS)
        check(add(MARKER, NO_ID, NO_ID, NO_ID, NO_ID, 0) == REACHED_ALL)
    }

    /** The number of origins, the markers included. */
    val size: Int get() = kinds.size

    /** The origin `Sym(base, [])`: the base value itself. */
    fun root(base: BaseId): OriginId {
        val known = roots.get(base)
        if (known != NO_ID) return known
        val o = add(SYM, base, NO_ID, NO_ID, 0, 0)
        roots.put(base, o)
        return o
    }

    /** The origin `Deep(base)`. */
    fun deep(base: BaseId): OriginId {
        val known = deeps.get(base)
        if (known != NO_ID) return known
        val o = add(DEEP, base, NO_ID, NO_ID, NO_ID, 0)
        deeps.put(base, o)
        return o
    }

    fun allocNew(site: SiteId): OriginId {
        val known = allocNews.get(site)
        if (known != NO_ID) return known
        val o = add(ALLOC_NEW, site, NO_ID, NO_ID, NO_ID, 0)
        allocNews.put(site, o)
        sites.noteAllocNew(site)
        return o
    }

    fun allocOld(site: SiteId): OriginId {
        val known = allocOlds.get(site)
        if (known != NO_ID) return known
        val o = add(ALLOC_OLD, site, NO_ID, NO_ID, NO_ID, 0)
        allocOlds.put(site, o)
        return o
    }

    /**
     * The name of cell [c] of origin [o]: the one origin of the default content (spec §3).
     * - `Sym(b, q)` with `|q| < K`: `Sym(b, q.c)`.
     * - `Sym(b, q)` with `|q| = K`, and `Deep(b)`: `Deep(b)`.
     * - `AllocNew(s)`, `AllocOld(s)`: `Sym(ALLOC_CHILD(s, c), [])`.
     */
    fun child(o: OriginId, c: CellId): OriginId = when (kinds.getInt(o)) {
        SYM -> {
            if (depths.getInt(o) < symDepth) symChild(o, c) else deep(payloads.getInt(o))
        }
        DEEP -> o
        ALLOC_NEW, ALLOC_OLD -> root(bases.allocChild(payloads.getInt(o), c))
        else -> error("A marker has no cells: $o")
    }

    /** As [child], but [NO_ID] if the child origin does not exist. It never makes an origin. */
    fun findChild(o: OriginId, c: CellId): OriginId = when (kinds.getInt(o)) {
        SYM -> {
            if (depths.getInt(o) < symDepth) {
                children.get(heapKey(o, c))
            } else {
                deeps.get(payloads.getInt(o))
            }
        }
        DEEP -> o
        ALLOC_NEW, ALLOC_OLD -> {
            val b = bases.findAllocChild(payloads.getInt(o), c)
            if (b == NO_ID) NO_ID else roots.get(b)
        }
        else -> NO_ID
    }

    /** The default content of cell [c] of origin [o]: the node `{child(o, c)}`. Cached for each heap key. */
    fun defaultNode(o: OriginId, c: CellId): NodeId {
        val key = heapKey(o, c)
        val known = defaults.get(key)
        if (known != NO_ID) return known
        val n = nodes.singleton(child(o, c))
        if (!frozen) defaults.put(key, n)
        return n
    }

    fun key(o: OriginId): OriginKey = when (kinds.getInt(o)) {
        SYM -> OriginKey.Sym(payloads.getInt(o), parents.getInt(o), cells.getInt(o))
        DEEP -> OriginKey.Deep(payloads.getInt(o))
        ALLOC_NEW -> OriginKey.AllocNew(payloads.getInt(o))
        ALLOC_OLD -> OriginKey.AllocOld(payloads.getInt(o))
        else -> if (o == REACHED_STATICS) OriginKey.ReachedStatics else OriginKey.ReachedAll
    }

    fun isSym(o: OriginId): Boolean = kinds.getInt(o) == SYM
    fun isDeep(o: OriginId): Boolean = kinds.getInt(o) == DEEP
    fun isAllocNew(o: OriginId): Boolean = kinds.getInt(o) == ALLOC_NEW
    fun isAllocOld(o: OriginId): Boolean = kinds.getInt(o) == ALLOC_OLD
    fun isAlloc(o: OriginId): Boolean = kinds.getInt(o).let { it == ALLOC_NEW || it == ALLOC_OLD }
    fun isMarker(o: OriginId): Boolean = kinds.getInt(o) == MARKER

    /** The base of a `Sym` or `Deep` origin, else [NO_ID]. */
    fun base(o: OriginId): BaseId = when (kinds.getInt(o)) {
        SYM, DEEP -> payloads.getInt(o)
        else -> NO_ID
    }

    /** The kind of the base of a `Sym` or `Deep` origin, else `null`. */
    fun baseKind(o: OriginId): BaseKind? {
        val b = base(o)
        return if (b == NO_ID) null else bases.kind(b)
    }

    /** The site of an `AllocNew` or `AllocOld` origin, else [NO_ID]. */
    fun site(o: OriginId): SiteId = if (isAlloc(o)) payloads.getInt(o) else NO_ID

    /** The parent of a `Sym` origin. [NO_ID] for a base value and for other origins. */
    fun parent(o: OriginId): OriginId = parents.getInt(o)

    /** The last cell of a `Sym` origin. [NO_ID] for a base value and for other origins. */
    fun cell(o: OriginId): CellId = cells.getInt(o)

    /** The path length of a `Sym` origin. [NO_ID] for other origins. */
    fun depth(o: OriginId): Int = depths.getInt(o)

    /** True if the path of a `Sym` origin has [ELEM_CELL]. */
    fun hasElemCell(o: OriginId): Boolean = elemFlags.getInt(o) != 0

    /**
     * The uniqueness by kind (IMPL §3.2). `entryUnique` is on (D1).
     * - `Sym` of `THIS`, `ARG`, `STATIC`: unique if the path has no [ELEM_CELL].
     * - `Sym` of `FRESH(s)`: unique if `s` is not a loop site and the path has no [ELEM_CELL].
     * - `AllocNew(s)`: unique.
     * - `AllocOld`, `Deep`, `Sym` of `CONST`, `BOX`, `NULL`, `ALLOC_CHILD`, markers: not unique.
     */
    fun uniqueByKind(o: OriginId): Boolean = when (kinds.getInt(o)) {
        SYM -> {
            if (hasElemCell(o)) {
                false
            } else {
                val b = payloads.getInt(o)
                when (val key = bases.key(b)) {
                    BaseKey.This, is BaseKey.Arg, is BaseKey.Static -> true
                    is BaseKey.Fresh -> !sites.isLoopSite(key.site)
                    else -> false
                }
            }
        }
        ALLOC_NEW -> true
        else -> false
    }

    /** Calls [body] for each proper ancestor of a `Sym` origin, from the parent to the base value. */
    inline fun forEachProperAncestor(o: OriginId, body: (OriginId) -> Unit) {
        var p = parent(o)
        while (p != NO_ID) {
            body(p)
            p = parent(p)
        }
    }

    /** True if [a] is a proper ancestor of [o]. */
    fun isProperAncestor(a: OriginId, o: OriginId): Boolean {
        forEachProperAncestor(o) { if (it == a) return true }
        return false
    }

    fun freeze() {
        frozen = true
    }

    private fun symChild(o: OriginId, c: CellId): OriginId {
        val key = heapKey(o, c)
        val known = children.get(key)
        if (known != NO_ID) return known
        val elem = if (c == ELEM_CELL || hasElemCell(o)) 1 else 0
        val child = add(SYM, payloads.getInt(o), o, c, depths.getInt(o) + 1, elem)
        children.put(key, child)
        return child
    }

    private fun add(kind: Int, payload: Int, parent: Int, cell: Int, depth: Int, elem: Int): OriginId {
        check(!frozen) { "OriginTable is frozen: no new origin" }
        val o = kinds.size
        kinds.add(kind)
        payloads.add(payload)
        parents.add(parent)
        cells.add(cell)
        depths.add(depth)
        elemFlags.add(elem)
        return o
    }

    companion object {
        /** Each static root and each origin below it is reached. */
        const val REACHED_STATICS: OriginId = 0

        /** The closure budget ran out: no origin is unique. */
        const val REACHED_ALL: OriginId = 1

        private const val MARKER = 0
        private const val SYM = 1
        private const val DEEP = 2
        private const val ALLOC_NEW = 3
        private const val ALLOC_OLD = 4
    }
}
