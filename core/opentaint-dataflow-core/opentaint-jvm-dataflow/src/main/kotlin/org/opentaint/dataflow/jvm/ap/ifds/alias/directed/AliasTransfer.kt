package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.analysis.alias.AnalysisCancellation

/** The result of [AliasTransfer.join]: the state and the change bit. */
data class Joined(val state: AliasState, val changed: Boolean)

/** A state and the node of an evaluated value expression. */
data class Evaluated(val state: AliasState, val node: NodeId)

/**
 * The transfer of the directed engine for the statements without calls (IMPL §4.1-§4.3), and the
 * join (IMPL §4.6). It uses the tables of one method. It does not use JIR.
 *
 * Reference: Lean `Impl/EngineState.lean` (`putH`, `storeE`, `joinE`, `retireE`) and
 * `Sound/ValueSem/Concept.lean` (`astepVS`, `retireV`, `adefaultV`).
 *
 * [cancellation]: a join and a retire call its checkpoint one time for each 1024 steps (IMPL §5.2).
 */
class AliasTransfer(val tables: AliasTables, private val cancellation: AnalysisCancellation? = null) {
    private val nodes = tables.nodes
    private val origins = tables.origins
    private val bases = tables.bases
    private val sites = tables.sites

    private val thisNode: NodeId by lazy { nodes.singleton(origins.root(bases.thisBase())) }

    private var steps = 0

    /** One step of a join or a retire. Each 1024 steps call the cancellation checkpoint. */
    private fun step() {
        if (cancellation != null && (++steps and STEP_MASK) == 0) cancellation.checkpoint()
    }

    /** The state after [instr]. An instruction that changes nothing gives the same instance. */
    fun transfer(st: AliasState, instr: AliasInstr): AliasState = when (instr) {
        is AliasInstr.Assign -> {
            val (s, n) = evaluate(st, instr.value)
            setVar(s, instr.dst, n)
        }

        is AliasInstr.StaticRead -> {
            val n = origins.defaultNode(origins.root(instr.staticBase), instr.cell)
            setVar(st, instr.dst, n)
        }

        is AliasInstr.FieldLoad -> setVar(st, instr.dst, load(st, valueNode(st, instr.base), instr.cell))
        is AliasInstr.ArrayLoad -> setVar(st, instr.dst, load(st, valueNode(st, instr.base), ELEM_CELL))

        is AliasInstr.FieldStore -> {
            val (s, v) = evaluate(st, instr.value)
            store(s, valueNode(s, instr.base), instr.cell, v)
        }

        is AliasInstr.ArrayStore -> {
            val (s, v) = evaluate(st, instr.value)
            storeWeak(s, valueNode(s, instr.base), ELEM_CELL, v)
        }

        AliasInstr.StaticWrite, AliasInstr.Nop, is AliasInstr.Return, is AliasInstr.Throw -> st

        is AliasInstr.UnresolvedCall -> throw NotImplementedError("Unresolved call: step T4")
        is AliasInstr.ResolvedCall -> throw NotImplementedError("Resolved call: step T6")
    }

    /** `val(v)`: `env[v]` of a local, or the root of `this` or of an argument by rule. */
    fun valueNode(st: AliasState, v: AliasValue.Ref): NodeId = when (v) {
        is AliasValue.Local -> st.varNode(v.v)
        AliasValue.This -> thisNode
        is AliasValue.Arg -> nodes.singleton(origins.root(bases.arg(v.index)))
    }

    /**
     * `value(v)`: evaluates a value expression with the `Assign` rules. Only `New` changes the
     * state (the retire of a loop site).
     */
    fun evaluate(st: AliasState, v: AliasValue): Evaluated = when (v) {
        is AliasValue.Ref -> Evaluated(st, valueNode(st, v))
        is AliasValue.New -> {
            val s = if (sites.isLoopSite(v.site)) retire(st, v.site) else st
            Evaluated(s, nodes.singleton(origins.allocNew(v.site)))
        }
        is AliasValue.Fresh -> Evaluated(st, rootNode(bases.fresh(v.site)))
        is AliasValue.Box -> Evaluated(st, rootNode(bases.box(v.site)))
        is AliasValue.Null -> Evaluated(st, rootNode(bases.nullAt(v.site)))
        is AliasValue.Const -> Evaluated(st, rootNode(v.base))
    }

    /** `read(o, c)`: `heap[(o, c)]`, or the default node by rule. */
    fun read(st: AliasState, o: OriginId, c: CellId): NodeId {
        val n = st.heapNode(heapKey(o, c))
        return if (n != NO_ID) n else origins.defaultNode(o, c)
    }

    /** `load(base, c)`: the union of `read(o, c)` for each origin `o` of [base] (spec §5.2). */
    fun load(st: AliasState, base: NodeId, c: CellId): NodeId {
        var acc = EMPTY_NODE
        for (o in nodes.members(base)) acc = nodes.union(acc, read(st, o, c))
        return acc
    }

    /** `put(o, c, n)`: removes the key if [n] is the default node, else writes [n] (`putH`). */
    fun put(st: AliasState, o: OriginId, c: CellId, n: NodeId): AliasState {
        val ed = edit(st)
        put(ed, o, c, n)
        return ed.build()
    }

    /**
     * The store of spec §5.3. Strong if [base] has one origin `o` and either `H(o, c) ⊆ v` (the
     * shortcut, `store_shortcut`) or `o` is unique. Else weak (`storeE`).
     */
    fun store(st: AliasState, base: NodeId, c: CellId, v: NodeId): AliasState {
        val os = nodes.members(base)
        if (os.size == 1) {
            val o = os[0]
            if (nodes.subset(read(st, o, c), v)) return put(st, o, c, v)
            if (isUnique(st, o)) return put(st, o, c, v)
        }
        return storeWeak(st, base, c, v)
    }

    /** The weak store: `H(o, c) := H(o, c) ∪ v` for each origin `o` of [base] (`weakE`). */
    fun storeWeak(st: AliasState, base: NodeId, c: CellId, v: NodeId): AliasState {
        val ed = edit(st)
        for (o in nodes.members(base)) {
            put(ed, o, c, nodes.union(read(ed, o, c), v))
        }
        return ed.build()
    }

    /**
     * The uniqueness test of the strong update (IMPL §4.2, spec §5.3; Lean `uniqueBO` with
     * `entryUnique` on):
     * 1. the origin is unique by kind;
     * 2. `Etree` has no [OriginTable.REACHED_ALL];
     * 3. if `Etree` has [OriginTable.REACHED_STATICS], the origin is not below a static root;
     * 4. no proper ancestor of the origin is in `Etree`;
     * 5. the origin is not in `Eval`.
     */
    fun isUnique(st: AliasState, o: OriginId): Boolean {
        if (!origins.uniqueByKind(o)) return false
        val etree = st.varNode(ETREE)
        val eval = st.varNode(EVAL)
        if (nodes.contains(etree, OriginTable.REACHED_ALL)) return false
        if (nodes.contains(etree, OriginTable.REACHED_STATICS) &&
            origins.baseKind(o) == BaseKind.STATIC && origins.depth(o) > 0
        ) return false
        if (etree != EMPTY_NODE) {
            origins.forEachProperAncestor(o) { if (nodes.contains(etree, it)) return false }
        }
        return !nodes.contains(eval, o)
    }

    /**
     * `retire(s)` (IMPL §4.3, spec §5.1; Lean `retireE`). The most recent object of the loop site
     * [s] becomes an older object:
     * 1. for each cell `c` written for `AllocNew(s)` or for `AllocOld(s)`:
     *    `H(old, c) := H(old, c) ∪ H(new, c)`, each side read by rule (`retireNaive_ne`);
     * 2. the cells of `AllocNew(s)` are removed, so the new object has its default content;
     * 3. `AllocNew(s)` becomes `AllocOld(s)` in each node of `env` (the reserved keys included)
     *    and of `heap`.
     *
     * It reads the two indexes of the state ([AliasIndex]): the written cells of the two origins,
     * and the holders of `AllocNew(s)`. It does not scan the state.
     */
    fun retire(st: AliasState, s: SiteId): AliasState {
        require(sites.isLoopSite(s)) { "Only a loop site retires: $s" }
        val nw = origins.allocNew(s)
        val old = origins.allocOld(s)
        val newCells = st.index.writtenCells(nw)
        val oldCells = st.index.writtenCells(old)
        if (newCells.isEmpty() && oldCells.isEmpty() && st.index.holders(nw).isEmpty()) return st
        val ed = edit(st)

        // Steps 1 and 2. A union that holds new(s) is renamed in step 3.
        if (newCells.isNotEmpty() || oldCells.isNotEmpty()) {
            val cells = IntOpenHashSet(newCells.size + oldCells.size)
            for (c in newCells) cells.add(c)
            for (c in oldCells) cells.add(c)
            val it = cells.iterator()
            while (it.hasNext()) {
                step()
                val c = it.nextInt()
                put(ed, old, c, nodes.union(read(st, old, c), read(st, nw, c)))
            }
            for (c in newCells) ed.removeHeap(heapKey(nw, c))
        }

        // Step 3: rename in each holder of new(s), after steps 1 and 2.
        val held = ed.holders(nw)
        for (v in held.vars) {
            step()
            ed.setVar(v, nodes.rename(ed.varNode(v), nw, old))
        }
        for (key in held.keys) {
            step()
            put(ed, heapKeyOrigin(key), heapKeyCell(key), nodes.rename(ed.heapNode(key), nw, old))
        }
        return ed.build()
    }

    /** An editor of [st] that keeps the holders index of this method. */
    fun edit(st: AliasState): AliasState.Editor = st.edit(tables.loopAllocs)

    /**
     * The join of two states (IMPL §4.6; Lean `joinE`). For each key in either map: one memoized
     * union. An absent env key is the empty set. An absent heap key is its default node. The
     * result is in normal form.
     *
     * [Joined.changed] is true if some key of the result holds a node that is not its node in [a].
     * If it is false, the result is [a] itself.
     */
    fun join(a: AliasState, b: AliasState): Joined {
        if (a === b) return Joined(a, false)
        val ed = edit(a)
        b.forEachVar { v, nb ->
            step()
            val na = a.varNode(v)
            ed.setVar(v, nodes.union(na, nb))
        }
        b.forEachHeap { key, nb ->
            step()
            val o = heapKeyOrigin(key)
            val c = heapKeyCell(key)
            val na = read(a, o, c)
            put(ed, o, c, nodes.union(na, nb))
        }
        // A key that only `a` has: its value in `b` is the empty set (env) or the default (heap).
        a.forEachHeap { key, na ->
            step()
            if (!b.isWritten(key)) {
                val o = heapKeyOrigin(key)
                val c = heapKeyCell(key)
                put(ed, o, c, nodes.union(na, origins.defaultNode(o, c)))
            }
        }
        val result = ed.build()
        return Joined(result, result !== a)
    }

    /**
     * Removes each local that [keep] rejects. The reserved keys [ETREE] and [EVAL] stay
     * (spec §5.5). The CFG step calls it with the live set of a node.
     */
    inline fun kill(st: AliasState, keep: (VarId) -> Boolean): AliasState {
        val ed = edit(st)
        st.forEachVar { v, _ ->
            if (v != ETREE && v != EVAL && !keep(v)) ed.removeVar(v)
        }
        return ed.build()
    }

    private fun setVar(st: AliasState, v: VarId, n: NodeId): AliasState {
        val ed = edit(st)
        ed.setVar(v, n)
        return ed.build()
    }

    private fun rootNode(b: BaseId): NodeId = nodes.singleton(origins.root(b))

    private fun read(ed: AliasState.Editor, o: OriginId, c: CellId): NodeId {
        val n = ed.heapNode(heapKey(o, c))
        return if (n != NO_ID) n else origins.defaultNode(o, c)
    }

    private fun put(ed: AliasState.Editor, o: OriginId, c: CellId, n: NodeId) {
        val key = heapKey(o, c)
        if (n == origins.defaultNode(o, c)) ed.removeHeap(key) else ed.setHeap(key, n)
    }

    private companion object {
        const val STEP_MASK = 1023
    }
}
