package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/**
 * The naive concept of design VS (IMPL §9.1 item 2, design §10.1 layer L1). It is a direct Kotlin
 * port of Lean `astepVS` (`Sound/ValueSem/Concept.lean`) with explicit sets:
 *
 * - The origins are values with their paths ([Origin]), not interned ids. A set is a [Set].
 * - The heap is total: an absent key holds its default content by rule (`adefaultV`, `childCN`).
 * - The call is `callVS`: the closure `R` of the start set over EACH CELL OF EACH COVERED ORIGIN
 *   OF THE FINITE UNIVERSE (`closeN`, `succsN`), `Etree ∪= R`, `Eval ∪= succsN(R)`, no heap write.
 * - `retireV` renames `new(s)` to `old(s)` everywhere, joins the cells of both origins into
 *   `old(s)`, and gives `new(s)` its default content. It runs at `new`, at an unknown expression
 *   and at a call, as in Lean (the engine retires only at a `new` of a loop site).
 * - The store is `storeBO`: strong if the base has one origin and `uniqueBO` holds (`uniqueR`,
 *   no proper prefix in `Etree` (`expB`), not in `Eval`). It has no shortcut.
 * - The universe and the static roots: each base of the CFG, with all paths up to K and the deep
 *   summary; the static roots are the static holders of the CFG (Lean `statics`).
 *
 * It runs on the same [AliasCfg] with the same WTO and the same edge rules as [DirectedFixpoint]
 * (entry, handlers, loop heads, kills). Only the state domain and the transfer are different.
 * It does not run inlined calls. It applies the pass-through models of a call (IMPL §4.5) as weak
 * copies after the call.
 *
 * @param tables the tables of the CFG. The concept reads only the keys of the ids (sites, cells,
 *   bases of constants and statics), never the origins or the nodes of the engine.
 * @param extraBases bases of the universe that no instruction has: the roots of an initial state.
 */
class NaiveConcept(
    private val tables: AliasTables,
    val cfg: AliasCfg,
    private val k: Int,
    extraBases: Collection<Base> = emptyList(),
) {

    /** The base of a symbolic origin. */
    sealed interface Base {
        data object This : Base
        data class Arg(val index: Int) : Base
        data class Static(val className: String) : Base
        data class Fresh(val site: SiteId) : Base
        data class Const(val type: String, val text: String) : Base
        data class Box(val site: SiteId) : Base
        data class Null(val site: SiteId) : Base
        data class AllocChild(val site: SiteId, val cell: CellId) : Base
    }

    /** An origin with its full name. */
    sealed interface Origin {
        data class Sym(val base: Base, val path: List<CellId>) : Origin
        data class Deep(val base: Base) : Origin
        data class New(val site: SiteId) : Origin
        data class Old(val site: SiteId) : Origin
    }

    data class Key(val o: Origin, val c: CellId)

    /** A state: `env`, the total heap (absent: default), `Etree` and `Eval`. Normal form: no default entry, no empty var. */
    data class State(
        val env: Map<VarId, Set<Origin>>,
        val heap: Map<Key, Set<Origin>>,
        val etree: Set<Origin>,
        val eval: Set<Origin>,
    )

    private val cells: List<CellId> = (0 until tables.cells.size).toList()
    private val once: Map<SiteId, Boolean>
    private val universe: List<Origin>
    private val staticRoots: Set<Origin>
    private val allocSiteSet: Set<SiteId>

    /** For each universe origin `u`: the origins whose subtree has `u` (Lean `descB a u`). */
    private val coverers: Map<Origin, List<Origin>>

    init {
        val count = HashMap<SiteId, Int>()
        val cyclic = HashMap<SiteId, Boolean>()
        val bases = LinkedHashSet<Base>()
        val allocSites = LinkedHashSet<SiteId>()
        for (v in 0 until cfg.size) {
            val instr = cfg.instr(v)
            val sites = HashSet<SiteId>()
            instr.forEachSite { sites += it }
            for (s in sites) {
                count[s] = (count[s] ?: 0) + 1
                if (cfg.onCycle(v)) cyclic[s] = true
            }
            collectBases(instr, bases, allocSites)
        }
        once = count.mapValues { (s, c) -> c == 1 && cyclic[s] != true }
        bases += extraBases
        for (s in allocSites) for (c in cells) bases += Base.AllocChild(s, c)
        val u = ArrayList<Origin>()
        for (b in bases) {
            for (p in pathsUpTo(k)) u += Origin.Sym(b, p)
            u += Origin.Deep(b)
        }
        for (s in allocSites) {
            u += Origin.New(s)
            u += Origin.Old(s)
        }
        universe = u
        allocSiteSet = allocSites
        staticRoots = bases.filterIsInstance<Base.Static>().map { Origin.Sym(it, emptyList()) }.toSet()
        coverers = universe.associateWith(::coverersOf)
    }

    // ---- The fixpoint, as DirectedFixpoint.Run. ----

    class Result(val before: Array<State?>, val after: Array<State?>)

    fun solve(initial: State = EMPTY): Result {
        val before = arrayOfNulls<State>(cfg.size)
        val after = arrayOfNulls<State>(cfg.size)

        fun inputs(v: Int): State? {
            var acc: State? = if (v == cfg.entry) initial else null
            for (p in cfg.normalPredecessors(v)) acc = join(acc, after[p])
            for (t in cfg.throwers(v)) {
                acc = join(acc, before[t])
                acc = join(acc, after[t])
            }
            return acc?.let { kill(v, it) }
        }

        fun evalNode(v: Int, st: State) {
            before[v] = st
            after[v] = transfer(st, cfg.instr(v))
        }

        fun stabilize(c: WtoComponent) {
            when (c) {
                is WtoComponent.Vertex -> inputs(c.node)?.let { evalNode(c.node, it) }
                is WtoComponent.Loop -> {
                    var acc: State? = null
                    var first = true
                    while (true) {
                        val input = inputs(c.head)
                        val next: State?
                        val changed: Boolean
                        when {
                            acc == null -> { next = input; changed = input != null }
                            input == null -> { next = acc; changed = false }
                            else -> { next = join(acc, input); changed = next != acc }
                        }
                        if (!first && !changed) break
                        first = false
                        acc = next
                        if (acc != null) evalNode(c.head, acc)
                        for (b in c.body) stabilize(b)
                    }
                }
            }
        }

        for (c in cfg.wto) stabilize(c)
        return Result(before, after)
    }

    // ---- The transfer (astepVS). ----

    fun transfer(st: State, instr: AliasInstr): State = when (instr) {
        is AliasInstr.Assign -> {
            val (s, v) = evaluate(st, instr.value)
            s.setVar(instr.dst, v)
        }
        is AliasInstr.StaticRead -> st.setVar(
            instr.dst, setOf(child(Origin.Sym(base(tables.bases.key(instr.staticBase)), emptyList()), instr.cell)),
        )
        is AliasInstr.FieldLoad -> st.setVar(instr.dst, load(st, value(st, instr.base), instr.cell))
        is AliasInstr.ArrayLoad -> st.setVar(instr.dst, load(st, value(st, instr.base), ELEM_CELL))
        is AliasInstr.FieldStore -> {
            val (s, v) = evaluate(st, instr.value)
            store(s, value(s, instr.base), instr.cell, v)
        }
        is AliasInstr.ArrayStore -> {
            val (s, v) = evaluate(st, instr.value)
            storeWeak(s, value(s, instr.base), ELEM_CELL, v)
        }
        AliasInstr.StaticWrite, AliasInstr.Nop, is AliasInstr.Return, is AliasInstr.Throw -> st
        is AliasInstr.UnresolvedCall -> models(st, call(st, instr.site, instr.result, instr.args), instr.result, instr.models)
        is AliasInstr.ResolvedCall -> {
            require(instr.callees === CalleeBodies.NONE) { "The naive concept does not inline" }
            models(st, call(st, instr.site, instr.result, instr.args), instr.result, instr.models)
        }
    }

    /**
     * The pass-through models of a call (IMPL §4.5): after the call, a weak copy `to ∪= pts(from)`
     * for each model, in its order. `pts(from)` reads [before] (the state before the call), except
     * a `from` on the result: it reads the current state. A target without cells is a variable: the
     * result or a local (`this`, an argument and a constant are not in `env`: no change). A target
     * with cells `c1..ck` is `storeWeak(load(val(base), c1..c(k-1)), ck, pts(from))`. A model on the
     * result of a call without a result variable has no effect.
     */
    private fun models(before: State, after: State, result: VarId?, models: List<PassThrough>): State {
        var cur = after
        for (m in models) {
            val fromState = if (m.from.base == ModelBase.Result) cur else before
            val fromBase = modelBase(fromState, m.from.base, result) ?: continue
            val from = m.from.cells.fold(fromBase) { s, c -> load(fromState, s, c) }
            if (m.to.cells.isEmpty()) {
                val v = when (val b = m.to.base) {
                    ModelBase.Result -> result
                    is ModelBase.Value -> (b.value as? AliasValue.Local)?.v
                } ?: continue
                cur = cur.setVar(v, (cur.env[v] ?: emptySet()) + from)
                continue
            }
            var base = modelBase(cur, m.to.base, result) ?: continue
            for (c in m.to.cells.dropLast(1)) base = load(cur, base, c)
            cur = storeWeak(cur, base, m.to.cells.last(), from)
        }
        return cur
    }

    private fun modelBase(st: State, base: ModelBase, result: VarId?): Set<Origin>? = when (base) {
        ModelBase.Result -> result?.let { st.env[it] ?: emptySet() }
        is ModelBase.Value -> evaluate(st, base.value).second
    }

    /** `x = m(args)` at `s`: `retireV s (callVS X args)`, then the result `⟨s⟩`. */
    private fun call(st: State, site: SiteId, result: VarId?, args: List<AliasValue>): State {
        val roots = HashSet<Origin>()
        for (a in args) roots += evaluate(st, a).second
        val retired = retire(callVS(st, roots), site)
        return if (result == null) retired else retired.setVar(result, setOf(Origin.Sym(Base.Fresh(site), emptyList())))
    }

    /** `callVS`: the closure of `closeN` over the universe; `Etree ∪= R`, `Eval ∪= succsN(R)`. */
    fun callVS(st: State, args: Set<Origin>): State {
        var r: Set<Origin> = args + staticRoots
        repeat(universe.size + 1) {
            val succ = succsN(st, r)
            if (r.containsAll(succ)) return st.copy(etree = st.etree + r, eval = st.eval + succ)
            r = r + succ
        }
        return st.copy(etree = st.etree + universe, eval = st.eval + universe)
    }

    /** `succsN`: the contents of each cell of each universe origin that [r] covers. */
    private fun succsN(st: State, r: Set<Origin>): Set<Origin> {
        val out = HashSet<Origin>()
        for (u in universe) {
            if (coverers.getValue(u).none { it in r }) continue
            for (c in cells) out += read(st, u, c)
        }
        return out
    }

    /** `retireV s`: `new(s)` becomes `old(s)`; the cells of both go to `old(s)`; `new(s)` gets its default cells. */
    fun retire(st: State, s: SiteId): State {
        val nw = Origin.New(s)
        val old = Origin.Old(s)
        // Without an allocation at s, no state has new(s) or old(s), and the retire is the identity.
        if (s !in allocSiteSet) return st
        fun rename(set: Set<Origin>): Set<Origin> = if (nw in set) set - nw + old else set
        val heap = HashMap<Key, Set<Origin>>()
        for ((key, v) in st.heap) {
            if (key.o == nw || key.o == old) continue
            heap[key] = rename(v)
        }
        for (c in cells) {
            val v = rename(read(st, nw, c) + read(st, old, c))
            if (v != setOf(child(old, c))) heap[Key(old, c)] = v
        }
        return State(st.env.mapValues { rename(it.value) }, heap, rename(st.etree), rename(st.eval))
    }

    /** `storeBO`: strong if the base has one origin and it is unique, else weak. */
    fun store(st: State, base: Set<Origin>, c: CellId, v: Set<Origin>): State {
        if (base.size == 1) {
            val o = base.single()
            if (isUnique(st, o)) return st.put(o, c, v)
        }
        return storeWeak(st, base, c, v)
    }

    fun storeWeak(st: State, base: Set<Origin>, c: CellId, v: Set<Origin>): State {
        var cur = st
        for (o in base) cur = cur.put(o, c, read(cur, o, c) + v)
        return cur
    }

    /** `uniqueBO` with `uniqueR` and `expB` (entryUnique on). */
    fun isUnique(st: State, o: Origin): Boolean {
        val byKind = when (o) {
            is Origin.New -> true
            is Origin.Old, is Origin.Deep -> false
            is Origin.Sym -> ELEM_CELL !in o.path && when (val b = o.base) {
                Base.This, is Base.Arg, is Base.Static -> true
                is Base.Fresh -> once[b.site] == true
                else -> false
            }
        }
        if (!byKind) return false
        if (o is Origin.Sym) {
            for (i in 0 until o.path.size) if (Origin.Sym(o.base, o.path.subList(0, i)) in st.etree) return false
        }
        return o !in st.eval
    }

    fun read(st: State, o: Origin, c: CellId): Set<Origin> = st.heap[Key(o, c)] ?: setOf(child(o, c))

    fun load(st: State, base: Set<Origin>, c: CellId): Set<Origin> {
        val out = HashSet<Origin>()
        for (o in base) out += read(st, o, c)
        return out
    }

    /** The default content (`childCN`): the name of cell [c] of [o]. */
    fun child(o: Origin, c: CellId): Origin = when (o) {
        is Origin.Sym -> if (o.path.size < k) Origin.Sym(o.base, o.path + c) else Origin.Deep(o.base)
        is Origin.Deep -> o
        is Origin.New -> Origin.Sym(Base.AllocChild(o.site, c), emptyList())
        is Origin.Old -> Origin.Sym(Base.AllocChild(o.site, c), emptyList())
    }

    fun join(a: State?, b: State?): State? {
        if (a == null) return b
        if (b == null) return a
        val env = HashMap(a.env)
        for ((v, s) in b.env) env[v] = (env[v] ?: emptySet()) + s
        val heap = HashMap<Key, Set<Origin>>()
        for (key in a.heap.keys + b.heap.keys) {
            val v = read(a, key.o, key.c) + read(b, key.o, key.c)
            if (v != setOf(child(key.o, key.c))) heap[key] = v
        }
        return State(env, heap, a.etree + b.etree, a.eval + b.eval)
    }

    fun kill(v: Int, st: State): State = st.copy(env = st.env.filterKeys { cfg.keepsAt(v, it) })

    private fun value(st: State, v: AliasValue.Ref): Set<Origin> = evaluate(st, v).second

    /** `value(v)` with the `Assign` rules. `new`, an unknown expression and a catch retire their site (`astepVS`). */
    fun evaluate(st: State, v: AliasValue): Pair<State, Set<Origin>> = when (v) {
        is AliasValue.Local -> st to (st.env[v.v] ?: emptySet())
        AliasValue.This -> st to setOf(Origin.Sym(Base.This, emptyList()))
        is AliasValue.Arg -> st to setOf(Origin.Sym(Base.Arg(v.index), emptyList()))
        is AliasValue.New -> retire(st, v.site) to setOf(Origin.New(v.site))
        is AliasValue.Fresh -> retire(st, v.site) to setOf(Origin.Sym(Base.Fresh(v.site), emptyList()))
        is AliasValue.Box -> st to setOf(Origin.Sym(Base.Box(v.site), emptyList()))
        is AliasValue.Null -> st to setOf(Origin.Sym(Base.Null(v.site), emptyList()))
        is AliasValue.Const -> st to setOf(Origin.Sym(base(tables.bases.key(v.base)), emptyList()))
    }

    private fun State.setVar(v: VarId, s: Set<Origin>): State =
        copy(env = if (s.isEmpty()) env - v else env + (v to s))

    private fun State.put(o: Origin, c: CellId, s: Set<Origin>): State {
        val key = Key(o, c)
        return copy(heap = if (s == setOf(child(o, c))) heap - key else heap + (key to s))
    }

    // ---- Names. ----

    /** The base of an engine base key. */
    fun base(key: BaseKey): Base = when (key) {
        BaseKey.This -> Base.This
        is BaseKey.Arg -> Base.Arg(key.index)
        is BaseKey.Static -> Base.Static(key.className)
        is BaseKey.Fresh -> Base.Fresh(key.site)
        is BaseKey.Const -> Base.Const(key.type, key.text)
        is BaseKey.Box -> Base.Box(key.site)
        is BaseKey.Null -> Base.Null(key.site)
        is BaseKey.AllocChild -> Base.AllocChild(key.site, key.cell)
    }

    /** The name of an engine origin (not a marker). */
    fun name(origins: OriginTable, o: OriginId): Origin = when (val key = origins.key(o)) {
        is OriginKey.Sym -> {
            val path = ArrayList<CellId>()
            var cur = o
            while (origins.parent(cur) != NO_ID) {
                path += origins.cell(cur)
                cur = origins.parent(cur)
            }
            path.reverse()
            Origin.Sym(base(tables.bases.key(key.base)), path)
        }
        is OriginKey.Deep -> Origin.Deep(base(tables.bases.key(key.base)))
        is OriginKey.AllocNew -> Origin.New(key.site)
        is OriginKey.AllocOld -> Origin.Old(key.site)
        OriginKey.ReachedStatics, OriginKey.ReachedAll -> error("A marker has no name: $o")
    }

    private fun collectBases(instr: AliasInstr, out: MutableSet<Base>, allocSites: MutableSet<SiteId>) {
        fun value(v: AliasValue?) {
            when (v) {
                null, is AliasValue.Local -> Unit
                AliasValue.This -> out += Base.This
                is AliasValue.Arg -> out += Base.Arg(v.index)
                is AliasValue.New -> allocSites += v.site
                is AliasValue.Fresh -> out += Base.Fresh(v.site)
                is AliasValue.Box -> out += Base.Box(v.site)
                is AliasValue.Null -> out += Base.Null(v.site)
                is AliasValue.Const -> out += base(tables.bases.key(v.base))
            }
        }
        when (instr) {
            is AliasInstr.Assign -> value(instr.value)
            is AliasInstr.StaticRead -> out += base(tables.bases.key(instr.staticBase))
            is AliasInstr.FieldLoad -> value(instr.base)
            is AliasInstr.ArrayLoad -> value(instr.base)
            is AliasInstr.FieldStore -> { value(instr.base); value(instr.value) }
            is AliasInstr.ArrayStore -> { value(instr.base); value(instr.value) }
            is AliasInstr.Return -> value(instr.value)
            is AliasInstr.Throw -> value(instr.value)
            is AliasInstr.UnresolvedCall -> { out += Base.Fresh(instr.site); instr.args.forEach(::value) }
            is AliasInstr.ResolvedCall -> { out += Base.Fresh(instr.site); instr.args.forEach(::value) }
            AliasInstr.StaticWrite, AliasInstr.Nop -> Unit
        }
    }

    private fun pathsUpTo(n: Int): List<List<CellId>> {
        if (n == 0) return listOf(emptyList())
        val shorter = pathsUpTo(n - 1)
        return listOf(emptyList<CellId>()) + cells.flatMap { c -> shorter.map { listOf(c) + it } }.distinct()
    }

    /** The origins `a` with `descB a u`: `u` itself, its path prefixes, and the allocation origins of its site. */
    private fun coverersOf(u: Origin): List<Origin> = when (u) {
        is Origin.Sym -> (0..u.path.size).map { Origin.Sym(u.base, u.path.subList(0, it)) } + allocOf(u.base)
        is Origin.Deep -> listOf(u) + universe.filter { it is Origin.Sym && it.base == u.base } + allocOf(u.base)
        is Origin.New, is Origin.Old -> listOf(u)
    }

    private fun allocOf(b: Base): List<Origin> =
        if (b is Base.AllocChild) listOf(Origin.New(b.site), Origin.Old(b.site)) else emptyList()

    companion object {
        val EMPTY = State(emptyMap(), emptyMap(), emptySet(), emptySet())
    }
}
