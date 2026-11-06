package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.random.Random

/**
 * A random concrete executor of an [AliasCfg] with instrumented values (IMPL §9.1 item 4). It is a
 * port of Lean `runAliasV` (`Sound/ValueSem/Run.lean`) and of the CFG steps of `Impl/Cfg.lean`
 * (`Step`, `IStep`, `XStep`), with the choices taken from a seeded [Random]:
 *
 * - Objects have names (`Obj`): the entry objects of `this`, of the arguments and of the static
 *   holders, and their paths (the entry heap is a tree, A1); the objects of an allocation site
 *   (`alloc(s, n)`); the result of the `n`-th run of an unknown expression, a call or a catch
 *   (`fresh(s, n)`); the objects that a callee writes (`havoc(s, n, k)`); the interned constants.
 * - A value is an object or a null instance with a tag (`VVal`, `NTag`): the default null of a
 *   cell of an allocated object, the `n`-th run of a null site, or a null that a callee writes.
 * - A cell is a field, or an array element with an index (0 or 1).
 * - A read or a write through a null blocks. A read of an unassigned local blocks (A4).
 * - A call writes new objects or new nulls into cells that its arguments or the static holders
 *   reach (narrow A2, `HavocN` with the callee nulls of `CalleeNull.lean`). The result is
 *   `fresh(s, n)`.
 * - An exceptional edge of a thrower has no effect, or, for a call, the callee writes and no
 *   result (`XStep`). The exception is unknown (A6): the catch gives a fresh object.
 *
 * [run] executes from the entry and calls the observer with each configuration (the node and
 * the state before it).
 */
class ConcreteExecutor(private val cfg: AliasCfg, private val tables: AliasTables, private val rnd: Random) {

    sealed interface CBase {
        data class Root(val name: String) : CBase
        data class Fresh(val site: SiteId, val n: Int) : CBase
        data class Havoc(val site: SiteId, val n: Int, val k: Int) : CBase
        data class Const(val base: BaseId) : CBase
    }

    /** A concrete cell: a field cell, or [ELEM_CELL] with an index. */
    data class CCell(val cell: CellId, val index: Int)

    sealed interface Obj {
        data class Sym(val base: CBase, val path: List<CCell>) : Obj
        data class Alloc(val site: SiteId, val n: Int) : Obj
    }

    sealed interface Tag {
        data class Dflt(val obj: Obj, val cell: CCell) : Tag
        data class Site(val site: SiteId, val n: Int) : Tag
        data class Callee(val site: SiteId, val n: Int, val k: Int) : Tag
    }

    sealed interface Value {
        data class O(val obj: Obj) : Value
        data class Nul(val tag: Tag) : Value
    }

    class State {
        val env = HashMap<VarId, Value>()
        val heap = HashMap<Pair<Obj, CCell>, Value>()
        val cnt = HashMap<SiteId, Int>()

        fun cell(o: Obj, c: CCell): Value = heap[o to c] ?: when (o) {
            is Obj.Sym -> Value.O(Obj.Sym(o.base, o.path + c))
            is Obj.Alloc -> Value.Nul(Tag.Dflt(o, c))
        }

        fun next(s: SiteId): Int = (cnt[s] ?: 0).also { cnt[s] = it + 1 }
    }

    private val fieldCells: List<CellId> = (1 until tables.cells.size).toList()
    private val allCells: List<CCell> = fieldCells.map { CCell(it, 0) } + listOf(CCell(ELEM_CELL, 0), CCell(ELEM_CELL, 1))
    private val staticRoots: List<Obj> = (0 until cfg.size).mapNotNull { v ->
        (cfg.instr(v) as? AliasInstr.StaticRead)?.let { staticHolder(it.staticBase) }
    }.distinct()

    /** The value of a root of the method: `this` or an argument. */
    fun rootValue(r: AliasValue.Ref, st: State): Value? = when (r) {
        is AliasValue.Local -> st.env[r.v]
        AliasValue.This -> Value.O(Obj.Sym(CBase.Root("this"), emptyList()))
        is AliasValue.Arg -> Value.O(Obj.Sym(CBase.Root("arg${r.index}"), emptyList()))
    }

    /** The cells of the paths of the alias check: the fields, and the array cell with index 0 and 1. */
    val checkCells: List<CCell> get() = allCells

    /** How a run ends. */
    enum class End { EXIT, BLOCKED, LIMIT }

    /**
     * Runs at most [maxSteps] steps from the entry. [observe] gets each node and the state before it.
     * At a node with more than one successor, the run prefers a successor whose step does not block
     * (a choice of the execution, so the run is still an execution of the CFG).
     */
    fun run(maxSteps: Int, observe: (Int, State) -> Unit): End {
        val st = State()
        var v = cfg.entry
        repeat(maxSteps) {
            observe(v, st)
            val handlers = cfg.handlers(v)
            val instr = cfg.instr(v)
            if (handlers.isNotEmpty() && (cfg.successors(v).isEmpty() || blocks(st, instr) || rnd.nextInt(5) == 0)) {
                if ((instr is AliasInstr.UnresolvedCall || instr is AliasInstr.ResolvedCall) && rnd.nextBoolean()) {
                    if (!call(st, instr, withResult = false)) return End.BLOCKED
                }
                v = handlers[rnd.nextInt(handlers.size)]
                return@repeat
            }
            if (!step(st, instr)) return End.BLOCKED
            val succ = cfg.successors(v)
            if (succ.isEmpty()) return End.EXIT
            val open = succ.filter { !blocks(st, cfg.instr(it)) }
            v = if (open.isNotEmpty()) open[rnd.nextInt(open.size)] else succ[rnd.nextInt(succ.size)]
        }
        return End.LIMIT
    }

    /** True if the normal step of [instr] blocks in [st]: a read of an unassigned local, or an access through null. */
    private fun blocks(st: State, instr: AliasInstr): Boolean {
        fun unassigned(v: AliasValue?) = v is AliasValue.Local && v.v !in st.env
        fun noObj(r: AliasValue.Ref) = rootValue(r, st) !is Value.O
        return when (instr) {
            is AliasInstr.Assign -> unassigned(instr.value)
            is AliasInstr.FieldLoad -> noObj(instr.base)
            is AliasInstr.ArrayLoad -> noObj(instr.base)
            is AliasInstr.FieldStore -> unassigned(instr.value) || noObj(instr.base)
            is AliasInstr.ArrayStore -> unassigned(instr.value) || noObj(instr.base)
            is AliasInstr.UnresolvedCall -> instr.args.any(::unassigned)
            is AliasInstr.ResolvedCall -> instr.args.any(::unassigned)
            else -> false
        }
    }

    /** One normal step. False: the step blocks. */
    private fun step(st: State, instr: AliasInstr): Boolean {
        when (instr) {
            is AliasInstr.Assign -> st.env[instr.dst] = eval(st, instr.value) ?: return false
            is AliasInstr.StaticRead -> st.env[instr.dst] = st.cell(staticHolder(instr.staticBase), CCell(instr.cell, 0))
            is AliasInstr.FieldLoad -> {
                val o = obj(st, instr.base) ?: return false
                st.env[instr.dst] = st.cell(o, CCell(instr.cell, 0))
            }
            is AliasInstr.ArrayLoad -> {
                val o = obj(st, instr.base) ?: return false
                st.env[instr.dst] = st.cell(o, CCell(ELEM_CELL, rnd.nextInt(2)))
            }
            is AliasInstr.FieldStore -> {
                val v = eval(st, instr.value) ?: return false
                val o = obj(st, instr.base) ?: return false
                st.heap[o to CCell(instr.cell, 0)] = v
            }
            is AliasInstr.ArrayStore -> {
                val v = eval(st, instr.value) ?: return false
                val o = obj(st, instr.base) ?: return false
                st.heap[o to CCell(ELEM_CELL, rnd.nextInt(2))] = v
            }
            is AliasInstr.UnresolvedCall, is AliasInstr.ResolvedCall -> return call(st, instr, withResult = true)
            AliasInstr.StaticWrite, AliasInstr.Nop, is AliasInstr.Return, is AliasInstr.Throw -> Unit
        }
        return true
    }

    /** A call: the callee writes into reached cells (narrow A2), then the result (if [withResult]). */
    private fun call(st: State, instr: AliasInstr, withResult: Boolean): Boolean {
        val (site, result, args) = when (instr) {
            is AliasInstr.UnresolvedCall -> Triple(instr.site, instr.result, instr.args)
            is AliasInstr.ResolvedCall -> Triple(instr.site, instr.result, instr.args)
            else -> error("not a call: $instr")
        }
        val starts = ArrayList<Obj>()
        for (a in args) {
            when (val v = eval(st, a) ?: return false) {
                is Value.O -> starts += v.obj
                is Value.Nul -> Unit
            }
        }
        starts += staticRoots
        val n = st.next(site)
        if (starts.isNotEmpty()) {
            repeat(rnd.nextInt(4)) { kIdx ->
                var o = starts[rnd.nextInt(starts.size)]
                repeat(rnd.nextInt(3)) {
                    val next = st.cell(o, allCells[rnd.nextInt(allCells.size)])
                    if (next is Value.O) o = next.obj
                }
                val c = allCells[rnd.nextInt(allCells.size)]
                st.heap[o to c] = if (rnd.nextInt(10) < 7) {
                    Value.O(Obj.Sym(CBase.Havoc(site, n, kIdx), emptyList()))
                } else {
                    Value.Nul(Tag.Callee(site, n, kIdx))
                }
            }
        }
        if (withResult && result != null) st.env[result] = Value.O(Obj.Sym(CBase.Fresh(site, n), emptyList()))
        return true
    }

    private fun obj(st: State, r: AliasValue.Ref): Obj? = (rootValue(r, st) as? Value.O)?.obj

    private fun eval(st: State, v: AliasValue): Value? = when (v) {
        is AliasValue.Ref -> rootValue(v, st)
        is AliasValue.New -> Value.O(Obj.Alloc(v.site, st.next(v.site)))
        is AliasValue.Fresh -> Value.O(Obj.Sym(CBase.Fresh(v.site, st.next(v.site)), emptyList()))
        is AliasValue.Box -> Value.O(Obj.Sym(CBase.Fresh(v.site, st.next(v.site)), emptyList()))
        is AliasValue.Null -> Value.Nul(Tag.Site(v.site, st.next(v.site)))
        is AliasValue.Const -> Value.O(Obj.Sym(CBase.Const(v.base), emptyList()))
    }

    private fun staticHolder(b: BaseId): Obj =
        Obj.Sym(CBase.Root("static:" + (tables.bases.key(b) as BaseKey.Static).className), emptyList())
}
