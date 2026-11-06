package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import java.util.concurrent.atomic.AtomicReferenceArray

/** The root of an answer path (IMPL §6.1 step 2). */
sealed interface PathRoot {
    /** A variable of the state: a local in a context. The state has an entry for it. */
    data class Var(val v: VarId) : PathRoot

    /** A root variable by rule: `this`, an argument, or a static holder. [base] is its base. */
    data class Base(val base: BaseId) : PathRoot
}

/** An answer path: [root] and the cells below it, at most D cells. */
data class AliasPath(val root: PathRoot, val cells: List<CellId>)

/**
 * The answer of one query: the alias [paths], and the [seeds] (the start set of the search).
 * The seeds are sorted. A seed with an id from [AliasQuery.originCount] is a query-local origin.
 * The conversion (IMPL §6.2) reads the items (allocations and constants) from the seeds.
 */
class QueryAnswer(val paths: List<AliasPath>, val seeds: IntArray)

/**
 * The backward query of the directed analysis (IMPL §6.1, §6.3, §6.4; spec §5.7). It does not use
 * JIR.
 *
 * The search starts from the seeds. A search node is a suffix `σ` and the set `G` of the origins
 * from which `σ` reaches a seed (Lean `Opt/Query.lean`, `search`). At each node:
 * 1. Output `(v, σ)` for each holder variable `v` of an origin of `G`: each variable of the state
 *    whose node holds it, and the root variable by rule of a base origin of `this`, of an
 *    argument, or of a static holder.
 * 2. For each cell `c`, the next set is the set of the holders `p` of `(p, c)` that hold an origin
 *    of `G` (Lean `holders_iff`): the written heap entries whose node holds it, and the default
 *    parent of a cell that is not written. Never expand the self cell of a `Deep` origin.
 * 3. Prefix the cell to the suffix, up to D = [maxAccessors] cells.
 * The search gives each path one time (`search_nodup`). The answer does not have the queried path.
 *
 * The universe of the search (ruling of the Task 5 review): the origins of the frozen tables, and
 * the query-local origins of this query (only a heap-path query makes them). The cells are the cells
 * of the table and the cells of the queried path. A cell id from the size of [CellTable] is a
 * query-local cell: the caller gives its meaning.
 * - The Lean search (`findAlias_iff`) has a wider universe: all paths up to K. There, the default
 *   parents of `Deep(b)` are all `Sym(b, q)` with `|q| = K`. Here they are only the depth-K origins
 *   of this universe. So the Lean answer has more paths: the paths through a depth-K origin that no
 *   state holds.
 * - This loses no real alias. Such an origin `⟨b.q⟩` is an entry path that no state ever held. By
 *   assumption A1 (the entry heap is a tree), it is a different object from each object that
 *   `deep(b)` stands for (the values deeper than K below `b` on the paths that the method reads).
 * - An enumeration of the depth-K origins would add up to `|cells|^k` paths of volume.
 * - The answer of a query does not depend on other queries: the query-local origins of one query are
 *   in its own [Scratch], never in the tables, in the reverse indexes or in a cache.
 *
 * A query never changes the tables: a read of a default cell that the analysis did not make gives a
 * query-local origin (IMPL §6.4).
 *
 * Thread safety: the tables are frozen. The reverse index of a state is made on the first query
 * of the state and kept in an [AtomicReferenceArray]. Each query has its own query-local table.
 */
class AliasQuery(val result: DirectedAliasResult, val maxAccessors: Int) {
    private val tables = result.tables
    private val nodes = tables.nodes
    private val origins = tables.origins
    private val bases = tables.bases
    private val symDepth = origins.symDepth

    /** The number of origins of the frozen table. A query-local origin has an id from this number. */
    val originCount: Int = origins.size

    private val cellCount = tables.cells.size
    private val baseCount = bases.size

    private val indexes = AtomicReferenceArray<ReverseIndex>(2 * result.statesBefore.size)

    /** For each base: the `Sym` origins of the table at depth K. They are the default parents of `Deep(base)`. */
    private val depthK: Int2ObjectOpenHashMap<IntArray> by lazy {
        val lists = Int2ObjectOpenHashMap<IntArrayList>()
        for (o in 0 until originCount) {
            if (!origins.isSym(o) || origins.depth(o) != symDepth) continue
            val b = origins.base(o)
            (lists.get(b) ?: IntArrayList().also { lists.put(b, it) }).add(o)
        }
        Int2ObjectOpenHashMap<IntArray>().also { m -> lists.forEach { (b, l) -> m.put(b, l.toIntArray()) } }
    }

    init {
        check(nodes.isFrozen) { "Freeze the tables before the queries" }
        require(maxAccessors >= 0) { "maxAccessors must not be negative: $maxAccessors" }
    }

    /** The state before or after [node], or `null` if the analysis did not reach [node]. */
    fun state(node: Int, after: Boolean): AliasState? =
        (if (after) result.statesAfter else result.statesBefore).getOrNull(node)

    /** `findAlias(root)` in the state before or after [node]. `null` if the node has no state. */
    fun findAlias(node: Int, after: Boolean, root: PathRoot): QueryAnswer? {
        val st = state(node, after) ?: return null
        val scratch = Scratch(EMPTY_CELLS)
        return search(node, after, st, scratch, rootValue(st, root, scratch), AliasPath(root, emptyList()))
    }

    /**
     * The heap-path query of `root.cells` (spec §5.7). The start set is the value of the path. The
     * answer does not have the path `root.cells`. `null` if the node has no state.
     */
    fun findHeapAlias(node: Int, after: Boolean, root: PathRoot, cells: IntArray): QueryAnswer? {
        val st = state(node, after) ?: return null
        val scratch = Scratch(cells)
        var value = rootValue(st, root, scratch)
        for (c in cells) value = read(st, value, c, scratch)
        return search(node, after, st, scratch, value, AliasPath(root, cells.toList()))
    }

    /** The array element query (IMPL §6.3): the heap-path query of `root[*]`. */
    fun findArrayElementAliases(node: Int, after: Boolean, root: PathRoot): QueryAnswer? =
        findHeapAlias(node, after, root, intArrayOf(ELEM_CELL))

    private fun rootValue(st: AliasState, root: PathRoot, scratch: Scratch): IntArray = when (root) {
        is PathRoot.Var -> nodes.members(st.varNode(root.v))
        is PathRoot.Base -> intArrayOf(scratch.root(root.base))
    }

    /** The union of `read(o, c)` for each origin `o` of [value] (spec §5.2). Sorted, no duplicates. */
    private fun read(st: AliasState, value: IntArray, c: CellId, scratch: Scratch): IntArray {
        val out = IntOpenHashSet()
        for (o in value) {
            val n = if (o < originCount) st.heapNode(heapKey(o, c)) else NO_ID
            if (n != NO_ID) {
                for (x in nodes.members(n)) out.add(x)
            } else {
                out.add(scratch.child(o, c))
            }
        }
        return out.toIntArray().also { it.sort() }
    }

    private fun index(node: Int, after: Boolean, st: AliasState): ReverseIndex {
        val slot = 2 * node + if (after) 1 else 0
        indexes.get(slot)?.let { return it }
        val made = ReverseIndex(st, nodes)
        return if (indexes.compareAndSet(slot, null, made)) made else indexes.get(slot)
    }

    private fun search(
        node: Int,
        after: Boolean,
        st: AliasState,
        scratch: Scratch,
        seeds: IntArray,
        exclude: AliasPath,
    ): QueryAnswer {
        val search = Search(st, index(node, after, st), scratch, exclude)
        search.node(maxAccessors, emptyList(), seeds)
        return QueryAnswer(search.out, seeds.copyOf())
    }

    private inner class Search(
        private val st: AliasState,
        private val index: ReverseIndex,
        private val scratch: Scratch,
        private val exclude: AliasPath,
    ) {
        val out = ArrayList<AliasPath>()

        /** The search node with remaining depth [j], suffix [suffix] and origin set [g] (sorted). */
        fun node(j: Int, suffix: List<CellId>, g: IntArray) {
            val roots = LinkedHashSet<PathRoot>()
            for (o in g) {
                if (o < originCount) index.forEachVar(o) { roots.add(PathRoot.Var(it)) }
                scratch.ruleRoot(o)?.let(roots::add)
            }
            for (r in roots) {
                val p = AliasPath(r, suffix)
                if (p != exclude) out.add(p)
            }
            if (j == 0) return

            val pre = Int2ObjectOpenHashMap<IntOpenHashSet>()
            fun add(c: CellId, p: OriginId) {
                (pre.get(c) ?: IntOpenHashSet().also { pre.put(c, it) }).add(p)
            }
            for (o in g) {
                val deep = scratch.isDeep(o)
                if (o < originCount) {
                    index.forEachKey(o) { key ->
                        val p = heapKeyOrigin(key)
                        if (!deep || p != o) add(heapKeyCell(key), p)
                    }
                }
                scratch.forEachDefaultParent(o) { p, c ->
                    if (p >= originCount || !st.isWritten(heapKey(p, c))) add(c, p)
                }
            }
            val cells = pre.keys.toIntArray().also { it.sort() }
            for (c in cells) {
                val next = pre.get(c).toIntArray().also { it.sort() }
                val nextSuffix = ArrayList<CellId>(suffix.size + 1).also { it.add(c); it.addAll(suffix) }
                node(j - 1, nextSuffix, next)
            }
        }
    }

    /**
     * The query-local origin table (IMPL §6.4). It gives the default content of a cell that the
     * analysis did not make, with the rules of [OriginTable.child], and it never changes the frozen
     * tables. A query-local origin has an id from [originCount]. A query-local base (an allocation
     * child `⟨@s.c⟩` that the table does not have) has an id from the size of [BaseTable].
     *
     * [queryCells]: the cells of the queried path. A cell from the size of [CellTable] is a cell of
     * the universe only for this query.
     */
    private inner class Scratch(queryCells: IntArray) {
        private val extraCells: IntArray = queryCells.filter { it >= cellCount }.distinct().toIntArray()

        private val vKinds = IntArrayList()
        private val vBases = IntArrayList()
        private val vParents = IntArrayList()
        private val vCells = IntArrayList()
        private val vDepths = IntArrayList()
        private val vRoots = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
        private val vDeeps = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
        private val vChildren = Long2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }

        private val vBaseSites = IntArrayList()
        private val vBaseCells = IntArrayList()
        private val vBaseIds = Long2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }

        private fun isVirtual(o: OriginId): Boolean = o >= originCount

        private fun vIndex(o: OriginId): Int = o - originCount

        fun isSym(o: OriginId): Boolean = if (isVirtual(o)) vKinds.getInt(vIndex(o)) == SYM else origins.isSym(o)

        fun isDeep(o: OriginId): Boolean = if (isVirtual(o)) vKinds.getInt(vIndex(o)) == DEEP else origins.isDeep(o)

        private fun base(o: OriginId): BaseId = if (isVirtual(o)) vBases.getInt(vIndex(o)) else origins.base(o)

        private fun parent(o: OriginId): OriginId = if (isVirtual(o)) vParents.getInt(vIndex(o)) else origins.parent(o)

        private fun cell(o: OriginId): CellId = if (isVirtual(o)) vCells.getInt(vIndex(o)) else origins.cell(o)

        private fun depth(o: OriginId): Int = if (isVirtual(o)) vDepths.getInt(vIndex(o)) else origins.depth(o)

        private fun baseKind(b: BaseId): BaseKind = if (b < baseCount) bases.kind(b) else BaseKind.ALLOC_CHILD

        /** The root variable by rule of [o]: the base origin of `this`, of an argument or of a static holder. */
        fun ruleRoot(o: OriginId): PathRoot? {
            if (!isSym(o) || parent(o) != NO_ID) return null
            val b = base(o)
            return when (baseKind(b)) {
                BaseKind.THIS, BaseKind.ARG, BaseKind.STATIC -> PathRoot.Base(b)
                else -> null
            }
        }

        /** The origin `Sym(b, [])`. */
        fun root(b: BaseId): OriginId {
            if (b < baseCount) {
                val known = origins.findRoot(b)
                if (known != NO_ID) return known
            }
            val known = vRoots.get(b)
            if (known != NO_ID) return known
            return add(SYM, b, NO_ID, NO_ID, 0).also { vRoots.put(b, it) }
        }

        private fun deep(b: BaseId): OriginId {
            if (b < baseCount) {
                val known = origins.findDeep(b)
                if (known != NO_ID) return known
            }
            val known = vDeeps.get(b)
            if (known != NO_ID) return known
            return add(DEEP, b, NO_ID, NO_ID, NO_ID).also { vDeeps.put(b, it) }
        }

        /** The cell name of `(o, c)`: the rule of [OriginTable.child]. */
        fun child(o: OriginId, c: CellId): OriginId {
            if (isSym(o)) {
                if (depth(o) >= symDepth) return deep(base(o))
                if (!isVirtual(o)) {
                    val known = origins.findChild(o, c)
                    if (known != NO_ID) return known
                }
                val key = heapKey(o, c)
                val known = vChildren.get(key)
                if (known != NO_ID) return known
                return add(SYM, base(o), o, c, depth(o) + 1).also { vChildren.put(key, it) }
            }
            if (isDeep(o)) return o
            check(!isVirtual(o) && origins.isAlloc(o)) { "A marker has no cells: $o" }
            val site = origins.site(o)
            var b = bases.findAllocChild(site, c)
            if (b == NO_ID) b = allocChildBase(site, c)
            return root(b)
        }

        private fun allocChildBase(site: SiteId, c: CellId): BaseId {
            val key = heapKey(site, c)
            val known = vBaseIds.get(key)
            if (known != NO_ID) return known
            val b = baseCount + vBaseSites.size
            vBaseSites.add(site)
            vBaseCells.add(c)
            vBaseIds.put(key, b)
            return b
        }

        /**
         * The default parents of [o] (Lean `holders_iff`, `dfltParent_sym`): the cells `(p, c)`
         * whose cell name is [o]. The caller drops the written cells.
         * - `Sym(b, q.c)`: the cell `c` of `Sym(b, q)`.
         * - `Sym(ALLOC_CHILD(s, c), [])`: the cell `c` of `AllocNew(s)` and of `AllocOld(s)`.
         * - `Deep(b)`: each cell of each `Sym(b, q)` with `|q| = K`. Not the self cells of `Deep(b)`.
         */
        inline fun forEachDefaultParent(o: OriginId, body: (OriginId, CellId) -> Unit) {
            if (isSym(o)) {
                val p = parent(o)
                if (p != NO_ID) {
                    body(p, cell(o))
                    return
                }
                val b = base(o)
                if (baseKind(b) != BaseKind.ALLOC_CHILD) return
                val site: SiteId
                val c: CellId
                if (b < baseCount) {
                    val key = bases.key(b) as BaseKey.AllocChild
                    site = key.site
                    c = key.cell
                } else {
                    site = vBaseSites.getInt(b - baseCount)
                    c = vBaseCells.getInt(b - baseCount)
                }
                val n = origins.findAllocNew(site)
                if (n != NO_ID) body(n, c)
                val old = origins.findAllocOld(site)
                if (old != NO_ID) body(old, c)
                return
            }
            if (!isDeep(o)) return
            val b = base(o)
            if (b < baseCount) {
                depthK.get(b)?.forEach { p -> forEachCell { c -> body(p, c) } }
            }
            for (i in 0 until vKinds.size) {
                if (vKinds.getInt(i) == SYM && vBases.getInt(i) == b && vDepths.getInt(i) == symDepth) {
                    val p = originCount + i
                    forEachCell { c -> body(p, c) }
                }
            }
        }

        /** The cells of the universe of this query. */
        private inline fun forEachCell(body: (CellId) -> Unit) {
            for (c in 0 until cellCount) body(c)
            for (c in extraCells) body(c)
        }

        private fun add(kind: Int, base: BaseId, parent: OriginId, cell: CellId, depth: Int): OriginId {
            val o = originCount + vKinds.size
            vKinds.add(kind)
            vBases.add(base)
            vParents.add(parent)
            vCells.add(cell)
            vDepths.add(depth)
            return o
        }
    }

    /**
     * The reverse index of one state: for each origin, the variables and the written heap keys
     * whose node holds it. The reserved keys [ETREE] and [EVAL] are not holders.
     */
    private class ReverseIndex(st: AliasState, nodes: NodeTable) {
        private val vars = Int2ObjectOpenHashMap<IntArrayList>()
        private val keys = Int2ObjectOpenHashMap<LongArrayList>()

        init {
            st.forEachVar { v, n ->
                if (v != ETREE && v != EVAL) {
                    for (o in nodes.members(n)) (vars.get(o) ?: IntArrayList().also { vars.put(o, it) }).add(v)
                }
            }
            st.forEachHeap { k, n ->
                for (o in nodes.members(n)) (keys.get(o) ?: LongArrayList().also { keys.put(o, it) }).add(k)
            }
        }

        inline fun forEachVar(o: OriginId, body: (VarId) -> Unit) {
            val l = vars.get(o) ?: return
            for (i in 0 until l.size) body(l.getInt(i))
        }

        inline fun forEachKey(o: OriginId, body: (HeapKey) -> Unit) {
            val l = keys.get(o) ?: return
            for (i in 0 until l.size) body(l.getLong(i))
        }
    }

    private companion object {
        val EMPTY_CELLS = IntArray(0)
        const val SYM = 1
        const val DEEP = 2
    }
}
