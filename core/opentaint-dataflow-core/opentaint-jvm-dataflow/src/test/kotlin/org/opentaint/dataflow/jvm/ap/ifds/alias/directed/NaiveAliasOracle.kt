package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.JIRCallResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.Params
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalVariableReachability
import org.opentaint.dataflow.jvm.ap.ifds.alias.TaintRulesCallModelProvider
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.NaiveConcept.Base
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.NaiveConcept.Origin
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.graph.JApplicationGraph

/**
 * The expected answers of the directed facade for one JIR method, from [NaiveConcept] (IMPL §9.1
 * item 2). The probe tests in `DIRECTED` mode use it (IMPL §9 step T7).
 *
 * - The CFG: the lowering of the engine ([JIRAliasInliner.rootCfg]) at inlining depth 0. The
 *   pass-through models come from [rules], as in the facade.
 * - The states: [NaiveConcept.solve]. The engine transfer, fixpoint and query do not run.
 * - The answers: the naive enumeration of spec §5.7. Each root (a local of the state, `this`, an
 *   argument, a static holder) and each path of at most D cells below it is an answer if the value
 *   of the path has a seed. A step never goes from a deep summary to itself. A step from a depth-K
 *   origin through an unwritten cell to the deep summary needs the depth-K origin in some naive
 *   state (the universe ruling of Task 5, with the naive states in place of the engine tables).
 * - The conversion: the rules of IMPL §6.2, written again from the table of the proposal.
 *
 * It answers only the queries of the probe tests: [findAlias], [findHeapAlias] and
 * [findArrayElementAliases], all in the state before the statement.
 */
class NaiveAliasOracle(
    entryPoint: JIRInst,
    graph: JApplicationGraph,
    callResolver: JIRCallResolver,
    rules: TaintRulesProvider?,
    private val reachability: JIRLocalVariableReachability,
    private val languageManager: JIRLanguageManager,
    params: Params,
) {
    private val tables = AliasTables(params.symDepth)
    private val maxAccessors = params.maxAccessors
    private val cfg: AliasCfg
    private val naive: NaiveConcept
    private val result: NaiveConcept.Result

    /**
     * The origins of the locals and of the written heap of all naive states: the stand-in for the
     * origin table of the engine. `Etree` and `Eval` are not in it: the naive call puts each covered
     * origin of the universe into them, and the engine makes no origin in a call.
     */
    private val known: Set<Origin>

    /** The roots by rule: the base origins of `this`, of the arguments and of the static holders. */
    private val ruleRoots: List<Origin.Sym>

    init {
        require(params.aliasAnalysisInterProcCallDepth == 0) { "The naive concept does not inline" }
        val inliner = JIRAliasInliner(
            tables, graph, languageManager, callResolver, TaintRulesCallModelProvider(rules), params,
        )
        cfg = inliner.rootCfg(entryPoint)
        naive = NaiveConcept(tables, cfg, params.symDepth)
        result = naive.solve()

        val all = HashSet<Origin>()
        for (st in result.before.asList() + result.after.asList()) {
            if (st == null) continue
            st.env.values.forEach { all += it }
            for ((key, v) in st.heap) {
                all += key.o
                all += v
            }
        }
        known = all

        // The engine interns the bases of `this` and of the arguments in the transfer, so the
        // lowering tables can miss them: the roots come from the bases of the naive origins.
        ruleRoots = all.mapNotNull { o ->
            val b = (o as? Origin.Sym)?.base ?: (o as? Origin.Deep)?.base
            b.takeIf { it is Base.This || it is Base.Arg || it is Base.Static }
        }.distinct().map { Origin.Sym(it, emptyList()) }
    }

    /** The answer of `findAlias(local, statement)`. `null` if the statement has no state or the local is unknown. */
    fun findAlias(localIdx: Int, statement: CommonInst): List<AliasInfo>? {
        val stmt = languageManager.getInstIndex(statement)
        val st = result.before.getOrNull(stmt) ?: return null
        val v = tables.vars.find(localIdx, ROOT_CONTEXT).takeIf { it != NO_ID } ?: return null
        val seeds = st.env[v] ?: emptySet()
        return answer(st, stmt, seeds, Root.Var(v) to emptyList(), emptyMap(), items = true, query = emptySet())
    }

    /** The answer of the array element query of the local (IMPL §6.3). */
    fun findArrayElementAliases(localIdx: Int, statement: CommonInst): List<AliasInfo>? =
        heapQuery(localIdx, listOf(AliasAccessor.Array), statement, items = true)

    /** The answer of the heap-path query `local.path` (spec §5.7): paths only. */
    fun findHeapAlias(localIdx: Int, path: List<AliasAccessor>, statement: CommonInst): List<AliasInfo>? =
        heapQuery(localIdx, path, statement, items = false)

    private fun heapQuery(localIdx: Int, path: List<AliasAccessor>, statement: CommonInst, items: Boolean): List<AliasInfo>? {
        val stmt = languageManager.getInstIndex(statement)
        val st = result.before.getOrNull(stmt) ?: return null
        val v = tables.vars.find(localIdx, ROOT_CONTEXT).takeIf { it != NO_ID } ?: return null
        val extra = HashMap<CellId, AliasAccessor>()
        val cells = path.map { a ->
            when (a) {
                AliasAccessor.Array -> ELEM_CELL
                is AliasAccessor.Field -> tables.cells.find(a.className, a.fieldName, a.fieldType).takeIf { it != NO_ID }
                    ?: extra.entries.firstOrNull { it.value == a }?.key
                    ?: (tables.cells.size + extra.size).also { extra[it] = a }
                is AliasAccessor.Static -> return emptyList()
            }
        }
        // The origins on the queried path are origins of this query (engine: the query-local table).
        val query = HashSet<Origin>()
        var value = st.env[v] ?: emptySet()
        for (c in cells) {
            query += value
            value = naive.load(st, value, c)
        }
        return answer(st, stmt, value, Root.Var(v) to cells, extra, items, query)
    }

    private sealed interface Root {
        data class Var(val v: VarId) : Root
        data class Rule(val base: Base) : Root
    }

    private fun answer(
        st: NaiveConcept.State,
        stmt: Int,
        seeds: Set<Origin>,
        exclude: Pair<Root, List<CellId>>,
        extraCells: Map<CellId, AliasAccessor>,
        items: Boolean,
        query: Set<Origin>,
    ): List<AliasInfo> {
        val cells = (0 until tables.cells.size).toList() + extraCells.keys.sorted()
        val paths = LinkedHashSet<Pair<Root, List<CellId>>>()

        fun walk(root: Root, path: List<CellId>, set: Set<Origin>) {
            if (set.isEmpty()) return
            if (set.any { it in seeds } && (root to path) != exclude) paths += root to path
            if (path.size == maxAccessors) return
            for (c in cells) {
                val next = HashSet<Origin>()
                for (o in set) {
                    val written = st.heap.containsKey(NaiveConcept.Key(o, c))
                    for (o2 in naive.read(st, o, c)) {
                        if (o2 == o && o is Origin.Deep) continue
                        if (!written && o2 is Origin.Deep && o is Origin.Sym && o !in known && o !in query) continue
                        next += o2
                    }
                }
                walk(root, path + c, next)
            }
        }

        if (seeds.isNotEmpty()) {
            for ((v, s) in st.env) walk(Root.Var(v), emptyList(), s)
            for (o in ruleRoots) walk(Root.Rule(o.base), emptyList(), setOf(o))
        }

        val out = java.util.TreeSet(AliasInfoOrder)
        for ((root, path) in paths) convertPath(root, path, stmt, extraCells)?.let(out::add)
        if (items) for (o in seeds) addItems(o, out)
        return out.toList()
    }

    /** IMPL §6.2: a path from a root-context local, `this`, an argument or a static holder. */
    private fun convertPath(root: Root, path: List<CellId>, stmt: Int, extraCells: Map<CellId, AliasAccessor>): AliasApInfo? {
        val accessors = path.map { c ->
            when {
                c == ELEM_CELL -> AliasAccessor.Array
                c >= tables.cells.size -> extraCells.getValue(c)
                else -> tables.cells.fieldKey(c)!!.let { AliasAccessor.Field(it.className, it.fieldName, it.type) }
            }
        }
        return when (root) {
            is Root.Var -> {
                val key = tables.vars.key(root.v) ?: return null
                if (key.context != ROOT_CONTEXT) return null
                val base = AccessPathBase.LocalVar(key.index)
                if (!reachability.isReachable(base, stmt)) return null
                AliasApInfo(base, accessors)
            }
            is Root.Rule -> when (val b = root.base) {
                Base.This -> AliasApInfo(AccessPathBase.This, accessors)
                is Base.Arg -> AliasApInfo(AccessPathBase.Argument(b.index), accessors)
                is Base.Static -> {
                    val id = tables.bases.find(BaseKey.Static(b.className))
                    val typeName = id.takeIf { it != NO_ID }?.let { tables.bases.staticTypeName(it) } ?: b.className
                    AliasApInfo(AccessPathBase.ClassStatic, listOf(AliasAccessor.Static(typeName)) + accessors)
                }
                else -> null
            }
        }
    }

    /** IMPL §6.2: the items of a seed (allocations, boxes and constants of the root context). */
    private fun addItems(o: Origin, out: MutableSet<AliasInfo>) {
        when (o) {
            is Origin.New -> rootSite(o.site)?.let { out += AliasAllocInfo(it) }
            is Origin.Old -> rootSite(o.site)?.let { out += AliasAllocInfo(it) }
            is Origin.Deep -> Unit
            is Origin.Sym -> {
                if (o.path.isNotEmpty()) return
                when (val b = o.base) {
                    is Base.Const -> if (b.type == STRING_TYPE) {
                        out += AliasApInfo(AccessPathBase.Constant(STRING_TYPE, b.text), emptyList())
                    } else {
                        for (v in 0 until cfg.size) {
                            val value = when (val instr = cfg.instr(v)) {
                                is AliasInstr.Assign -> instr.value
                                is AliasInstr.FieldStore -> instr.value
                                is AliasInstr.ArrayStore -> instr.value
                                else -> null
                            }
                            if (value is AliasValue.Const && naive.base(tables.bases.key(value.base)) == b) {
                                out += AliasAllocInfo(v)
                            }
                        }
                    }
                    is Base.Box -> rootSite(b.site)?.let { out += AliasAllocInfo(it) }
                    else -> Unit
                }
            }
        }
    }

    private fun rootSite(s: SiteId): Int? {
        val key = tables.sites.key(s)
        return if (key.context == ROOT_CONTEXT) key.instIndex else null
    }
}
