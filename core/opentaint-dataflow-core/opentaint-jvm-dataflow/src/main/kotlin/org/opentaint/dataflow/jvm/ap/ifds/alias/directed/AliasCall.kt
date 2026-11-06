package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntArrays
import it.unimi.dsi.fastutil.ints.IntOpenHashSet

/** The default budget of the call closure (`JIRLocalAliasAnalysis.Params.maxCallClosure`). */
const val DEFAULT_MAX_CALL_CLOSURE: Int = 10_000

/**
 * The unresolved call (IMPL §4.4, §4.5; spec §5.6). Reference: Lean `Impl/EngineCall.lean`
 * (`closeE`, `callE`, `canU`, `isSymB`) and `Sound/ValueSem/Concept.lean` (`callVS`).
 *
 * The call is passive. It writes no heap entry. It adds the reached origins to `Etree` and the
 * reached cell contents to `Eval`, so later strong updates through them are weak. The result gets
 * `{Sym(FRESH(s))}`. Then the pass-through models of the callee are weak copies.
 *
 * [maxCallClosure]: the budget of the closure. Over it, both sets get [OriginTable.REACHED_ALL].
 */
class AliasCall(
    val transfer: AliasTransfer,
    val maxCallClosure: Int = DEFAULT_MAX_CALL_CLOSURE,
) {
    private val tables = transfer.tables
    private val nodes = tables.nodes
    private val origins = tables.origins

    private val reachedAll: NodeId by lazy { nodes.singleton(OriginTable.REACHED_ALL) }

    /**
     * The unresolved call at [site] (IMPL §4.1 table): `call(args)`, then `env[result] :=
     * {Sym(FRESH(site))}`, then the pass-through [models].
     */
    fun unresolved(
        st: AliasState,
        site: SiteId,
        result: VarId?,
        args: List<AliasValue>,
        models: List<PassThrough> = emptyList(),
    ): AliasState {
        var cur = call(st, roots(st, args))
        if (result != null) {
            val ed = transfer.edit(cur)
            ed.setVar(result, transfer.evaluate(cur, AliasValue.Fresh(site)).node)
            cur = ed.build()
        }
        for (m in models) cur = applyModel(st, cur, result, m)
        return cur
    }

    /** The union of the values of the arguments and of the receiver: the start set of the call. */
    fun roots(st: AliasState, args: List<AliasValue>): NodeId {
        var acc = EMPTY_NODE
        for (a in args) acc = nodes.union(acc, valueOf(st, a))
        return acc
    }

    /**
     * The passive call of IMPL §4.4 for the start set [roots]. `R` is [roots] and
     * [OriginTable.REACHED_STATICS]. The closure adds the content of each written cell that an
     * origin of `R` covers ([HeapIndex]), until `R` does not grow. Then `Etree ∪= ` the `Sym`
     * origins and the markers of `R`, and `Eval ∪= ` the contents of the covered written cells that
     * can be unique. If `R` gets larger than [maxCallClosure], both sets get
     * [OriginTable.REACHED_ALL]. The call writes no heap entry.
     */
    fun call(st: AliasState, roots: NodeId): AliasState {
        val index = HeapIndex(st)
        val reached = IntOpenHashSet()
        val vals = IntOpenHashSet()
        val work = IntArrayList()
        for (o in nodes.members(roots)) if (reached.add(o)) work.add(o)
        if (reached.add(OriginTable.REACHED_STATICS)) work.add(OriginTable.REACHED_STATICS)

        val counters = tables.counters
        counters.calls++
        while (!work.isEmpty) {
            if (reached.size > maxCallClosure) {
                counters.callFallbacks++
                counters.closureSizes.add(reached.size)
                return addSets(st, reachedAll, reachedAll)
            }
            transfer.step()
            val a = work.removeInt(work.size - 1)
            index.forEachCoveredBy(a) { w ->
                for (c in st.index.writtenCells(w)) {
                    transfer.step()
                    for (x in nodes.members(st.heapNode(heapKey(w, c)))) {
                        if (origins.uniqueByKind(x)) vals.add(x)
                        if (reached.add(x)) work.add(x)
                    }
                }
            }
        }

        counters.closureSizes.add(reached.size)
        val tree = IntArrayList(reached.size)
        val it = reached.iterator()
        while (it.hasNext()) {
            val o = it.nextInt()
            if (origins.isSym(o) || origins.isMarker(o)) tree.add(o)
        }
        return addSets(st, internSet(tree.toIntArray()), internSet(vals.toIntArray()))
    }

    /**
     * A pass-through model as a weak copy (IMPL §4.5). `pts(from)` reads [before] (the state before
     * the call), except a `from` on the result: it reads [cur]. The target is read in [cur].
     * - A target without cells: `env[v] ∪= pts(from)` for the result or for a local. `this`, an
     *   argument of the method and a constant are not variables of `env`: no change.
     * - A target with cells `c1..ck`: `storeWeak(load(val(base), c1..c(k-1)), ck, pts(from))`.
     * A model on the result of a call without a result variable has no effect.
     */
    private fun applyModel(before: AliasState, cur: AliasState, result: VarId?, m: PassThrough): AliasState {
        val fromState = if (m.from.base == ModelBase.Result) cur else before
        val from = pathNode(fromState, m.from, result) ?: return cur
        val to = m.to
        if (to.cells.isEmpty()) {
            val v = when (val b = to.base) {
                ModelBase.Result -> result
                is ModelBase.Value -> (b.value as? AliasValue.Local)?.v
            } ?: return cur
            val ed = transfer.edit(cur)
            ed.setVar(v, nodes.union(cur.varNode(v), from))
            return ed.build()
        }
        var base = baseNode(cur, to.base, result) ?: return cur
        for (i in 0 until to.cells.size - 1) base = transfer.load(cur, base, to.cells[i])
        return transfer.storeWeak(cur, base, to.cells.last(), from)
    }

    private fun pathNode(st: AliasState, path: ModelPath, result: VarId?): NodeId? {
        var n = baseNode(st, path.base, result) ?: return null
        for (c in path.cells) n = transfer.load(st, n, c)
        return n
    }

    private fun baseNode(st: AliasState, base: ModelBase, result: VarId?): NodeId? = when (base) {
        ModelBase.Result -> result?.let { st.varNode(it) }
        is ModelBase.Value -> valueOf(st, base.value)
    }

    /** The value of an argument. A call argument is never a `new` expression (no retire here). */
    private fun valueOf(st: AliasState, v: AliasValue): NodeId {
        require(v !is AliasValue.New) { "A call argument is not a new expression: $v" }
        return transfer.evaluate(st, v).node
    }

    private fun internSet(origins: IntArray): NodeId {
        if (origins.isEmpty()) return EMPTY_NODE
        IntArrays.quickSort(origins)
        return nodes.intern(origins)
    }

    /** `env[ETREE] ∪= etree`, `env[EVAL] ∪= eval`: two memoized unions. */
    private fun addSets(st: AliasState, etree: NodeId, eval: NodeId): AliasState {
        val ed = transfer.edit(st)
        ed.setVar(ETREE, nodes.union(st.varNode(ETREE), etree))
        ed.setVar(EVAL, nodes.union(st.varNode(EVAL), eval))
        return ed.build()
    }

    /**
     * The written heap keys of one state, grouped by the origins that cover them (IMPL §4.4). The
     * keys of one written origin `w` are one group. `w` is registered:
     * - under `w` itself and under each proper ancestor of `w` (a `Sym` parent chain);
     * - under its base, if `w` is `Deep(b)`: each `Sym` origin of base `b` covers it;
     * - under its site, if the base of `w` is `ALLOC_CHILD(s, c)`: `AllocNew(s)` and `AllocOld(s)`
     *   cover it;
     * - under [OriginTable.REACHED_STATICS], if the base of `w` is a `STATIC` base.
     * [forEachCoveredBy] gives each written origin one time only.
     */
    private inner class HeapIndex(st: AliasState) {
        private val byOrigin = Int2ObjectOpenHashMap<IntArrayList>()
        private val bySite = Int2ObjectOpenHashMap<IntArrayList>()
        private val deepByBase = Int2IntOpenHashMap().also { it.defaultReturnValue(NO_ID) }
        private val statics = IntArrayList()
        private val visited = IntOpenHashSet()

        init {
            for (w in st.index.writtenOrigins()) {
                transfer.step()
                add(byOrigin, w, w)
                origins.forEachProperAncestor(w) { add(byOrigin, it, w) }
                val b = origins.base(w)
                if (b == NO_ID) continue
                if (origins.isDeep(w)) deepByBase.put(b, w)
                when (val key = tables.bases.key(b)) {
                    is BaseKey.Static -> statics.add(w)
                    is BaseKey.AllocChild -> add(bySite, key.site, w)
                    else -> Unit
                }
            }
        }

        /** Calls [body] for each written origin that [a] covers and that no earlier call gave. */
        inline fun forEachCoveredBy(a: OriginId, body: (OriginId) -> Unit) {
            if (a == OriginTable.REACHED_STATICS) {
                visitAll(statics, body)
                return
            }
            if (origins.isMarker(a)) return
            visitAll(byOrigin.get(a), body)
            if (origins.isSym(a)) {
                val deep = deepByBase.get(origins.base(a))
                if (deep != NO_ID && visited.add(deep)) body(deep)
            } else if (origins.isAlloc(a)) {
                visitAll(bySite.get(origins.site(a)), body)
            }
        }

        private inline fun visitAll(list: IntArrayList?, body: (OriginId) -> Unit) {
            if (list == null) return
            for (i in 0 until list.size) {
                val w = list.getInt(i)
                if (visited.add(w)) body(w)
            }
        }

        private fun add(map: Int2ObjectOpenHashMap<IntArrayList>, key: Int, w: OriginId) {
            var list = map.get(key)
            if (list == null) {
                list = IntArrayList(2)
                map.put(key, list)
            }
            list.add(w)
        }
    }
}
