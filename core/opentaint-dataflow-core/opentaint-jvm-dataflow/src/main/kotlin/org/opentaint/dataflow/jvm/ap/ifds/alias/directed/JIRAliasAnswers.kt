package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAllocInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasInfo
import java.util.Collections
import java.util.concurrent.ConcurrentHashMap

/**
 * The answers of the directed analysis of one method as `AliasInfo` lists (IMPL §6.1-§6.4).
 *
 * Conversion of a [QueryAnswer] (IMPL §6.2):
 * - A path from a local of the root context: `AliasApInfo(LocalVar(i), accessors)`. The local must
 *   pass [isReachable] at the statement: `JIRLocalVariableReachability.isReachable`, as main's
 *   `compress`. A local of another context gives nothing.
 * - A path from `this` or an argument: `AliasApInfo(This / Argument(i), accessors)`.
 * - A path from a static holder `C`: `AliasApInfo(ClassStatic, [Static(type name of C)] + accessors)`.
 *   The type name is the name of main ([BaseTable.staticTypeName]).
 * - Items of the seeds (only `findAlias` and the array element query): `AllocNew(s)` or
 *   `AllocOld(s)` of the root context: `AliasAllocInfo(s)`. `const(String, v)`:
 *   `AliasApInfo(Constant("java.lang.String", v), [])`. Another constant (a box of a constant, a
 *   class literal): `AliasAllocInfo(i)` for each root-context statement `i` that makes it.
 *   `box(s)` of the root context: `AliasAllocInfo(s)`. `NULL`, `FRESH`, `ALLOC_CHILD` bases and
 *   their cells: nothing.
 *
 * The answer is an unmodifiable list, sorted with [AliasInfoOrder], with no duplicates. A cache
 * keyed by the statement, before or after, the local and the query kind keeps the full answers. So
 * the answers do not depend on the query order. The cache is a [ConcurrentHashMap]: the queries can
 * run in parallel threads, and they share the cached lists.
 */
internal class JIRAliasAnswers(
    private val result: DirectedAliasResult,
    private val isReachable: (AccessPathBase, Int) -> Boolean,
    maxAccessors: Int,
) {
    val query = AliasQuery(result, maxAccessors)

    private val tables = result.tables
    private val cache = ConcurrentHashMap<Long, List<AliasInfo>>()

    /** For each constant base: the root-context statements that make the constant. */
    private val constStatements: Int2ObjectOpenHashMap<IntArray> by lazy {
        val lists = Int2ObjectOpenHashMap<IntArrayList>()
        val cfg = result.cfg
        for (v in 0 until cfg.size) {
            val value = when (val instr = cfg.instr(v)) {
                is AliasInstr.Assign -> instr.value
                is AliasInstr.FieldStore -> instr.value
                is AliasInstr.ArrayStore -> instr.value
                else -> null
            }
            if (value !is AliasValue.Const) continue
            (lists.get(value.base) ?: IntArrayList().also { lists.put(value.base, it) }).add(v)
        }
        Int2ObjectOpenHashMap<IntArray>().also { m -> lists.forEach { (b, l) -> m.put(b, l.toIntArray()) } }
    }

    /**
     * The aliases of the local [localIdx] before ([after] false) or after the statement [stmt].
     * `null` if the statement has no state or the analysis does not know the local.
     */
    fun findAlias(localIdx: Int, stmt: Int, after: Boolean): List<AliasInfo>? {
        val v = rootLocal(localIdx, stmt, after) ?: return null
        return cached(if (after) KIND_AFTER else KIND_BEFORE, localIdx, stmt) {
            val answer = query.findAlias(stmt, after, PathRoot.Var(v)) ?: return null
            convert(answer, stmt, items = true, extraCells = emptyMap())
        }
    }

    /** The array element aliases of the local [localIdx] before [stmt] (IMPL §6.3). */
    fun findArrayElementAliases(localIdx: Int, stmt: Int): List<AliasInfo>? {
        val v = rootLocal(localIdx, stmt, after = false) ?: return null
        return cached(KIND_ELEMENTS, localIdx, stmt) {
            val answer = query.findArrayElementAliases(stmt, false, PathRoot.Var(v)) ?: return null
            convert(answer, stmt, items = true, extraCells = emptyMap())
        }
    }

    /**
     * The heap-path query of `local.path` before [stmt] (spec §5.7): the paths only, without the
     * queried path. A path with a static accessor gives an empty answer. Not cached (tests).
     */
    fun findHeapAlias(localIdx: Int, path: List<AliasAccessor>, stmt: Int): List<AliasInfo>? {
        val v = rootLocal(localIdx, stmt, after = false) ?: return null
        val cells = heapCells(path) ?: return emptyList()
        val answer = query.findHeapAlias(stmt, false, PathRoot.Var(v), cells.ids) ?: return null
        return convert(answer, stmt, items = false, extraCells = cells.extra)
    }

    /** The cells of a heap path: [ids] for the query, and the accessor of each query-local cell id. */
    class HeapCells(val ids: IntArray, val extra: Map<CellId, AliasAccessor>)

    /**
     * The cells of [path], or `null` for a path with a static accessor. A field that the table does
     * not have gets a query-local cell id (from the size of [CellTable]). Equal accessors get one id,
     * so `x.u.u` uses one id for `u`.
     */
    fun heapCells(path: List<AliasAccessor>): HeapCells? {
        val idOf = HashMap<AliasAccessor, CellId>()
        val extra = HashMap<CellId, AliasAccessor>()
        val ids = IntArray(path.size)
        for ((i, accessor) in path.withIndex()) {
            ids[i] = when (accessor) {
                AliasAccessor.Array -> ELEM_CELL
                is AliasAccessor.Field -> {
                    val c = tables.cells.find(accessor.className, accessor.fieldName, accessor.fieldType)
                    if (c != NO_ID) {
                        c
                    } else {
                        idOf.getOrPut(accessor) { (tables.cells.size + extra.size).also { extra[it] = accessor } }
                    }
                }
                is AliasAccessor.Static -> return null
            }
        }
        return HeapCells(ids, extra)
    }

    /** The root-context variable of a local, or `null` if the state or the variable is absent. */
    private fun rootLocal(localIdx: Int, stmt: Int, after: Boolean): VarId? {
        if (query.state(stmt, after) == null) return null
        return tables.vars.find(localIdx, ROOT_CONTEXT).takeIf { it != NO_ID }
    }

    private inline fun cached(kind: Int, localIdx: Int, stmt: Int, compute: () -> List<AliasInfo>): List<AliasInfo> {
        val key = (stmt.toLong() shl 32) or (localIdx.toLong() shl 2) or kind.toLong()
        cache[key]?.let { return it }
        val answer = compute()
        return cache.putIfAbsent(key, answer) ?: answer
    }

    private fun convert(
        answer: QueryAnswer,
        stmt: Int,
        items: Boolean,
        extraCells: Map<CellId, AliasAccessor>,
    ): List<AliasInfo> {
        val out = java.util.TreeSet(AliasInfoOrder)
        for (p in answer.paths) convertPath(p, stmt, extraCells)?.let(out::add)
        if (items) {
            for (o in answer.seeds) {
                if (o >= query.originCount) continue
                addItems(o, out)
            }
        }
        // The cache shares the list with all callers and threads: it must not change.
        return Collections.unmodifiableList(ArrayList(out))
    }

    private fun convertPath(p: AliasPath, stmt: Int, extraCells: Map<CellId, AliasAccessor>): AliasApInfo? {
        val accessors = p.cells.map { c ->
            when {
                c == ELEM_CELL -> AliasAccessor.Array
                c >= tables.cells.size -> extraCells.getValue(c)
                else -> {
                    val k = tables.cells.fieldKey(c)!!
                    AliasAccessor.Field(k.className, k.fieldName, k.type)
                }
            }
        }
        return when (val root = p.root) {
            is PathRoot.Var -> {
                val key = tables.vars.key(root.v) ?: return null
                if (key.context != ROOT_CONTEXT) return null
                val base = AccessPathBase.LocalVar(key.index)
                if (!isReachable(base, stmt)) return null
                AliasApInfo(base, accessors)
            }

            is PathRoot.Base -> when (val key = tables.bases.key(root.base)) {
                BaseKey.This -> AliasApInfo(AccessPathBase.This, accessors)
                is BaseKey.Arg -> AliasApInfo(AccessPathBase.Argument(key.index), accessors)
                is BaseKey.Static -> {
                    val typeName = tables.bases.staticTypeName(root.base) ?: key.className
                    AliasApInfo(AccessPathBase.ClassStatic, listOf(AliasAccessor.Static(typeName)) + accessors)
                }
                else -> null
            }
        }
    }

    private fun addItems(o: OriginId, out: MutableSet<AliasInfo>) {
        val origins = tables.origins
        if (origins.isAlloc(o)) {
            rootSite(origins.site(o))?.let { out.add(AliasAllocInfo(it)) }
            return
        }
        if (!origins.isSym(o) || origins.parent(o) != NO_ID) return
        val b = origins.base(o)
        when (val key = tables.bases.key(b)) {
            is BaseKey.Const -> {
                if (key.type == STRING_TYPE) {
                    out.add(AliasApInfo(AccessPathBase.Constant(STRING_TYPE, key.text), emptyList()))
                } else {
                    constStatements.get(b)?.forEach { out.add(AliasAllocInfo(it)) }
                }
            }

            is BaseKey.Box -> rootSite(key.site)?.let { out.add(AliasAllocInfo(it)) }
            else -> Unit
        }
    }

    /** The instruction index of a root-context site, or `null` for a site of another context. */
    private fun rootSite(s: SiteId): Int? {
        val key = tables.sites.key(s)
        return if (key.context == ROOT_CONTEXT) key.instIndex else null
    }

    private companion object {
        const val KIND_BEFORE = 0
        const val KIND_AFTER = 1
        const val KIND_ELEMENTS = 2
    }
}

/**
 * The fixed order of the directed answers (IMPL §6.2).
 *
 * 1. `AliasApInfo` before `AliasAllocInfo`.
 * 2. `AliasApInfo`: by the base, then by the number of accessors, then by the accessors one by one.
 *    Base order: `This`, `Argument` (by index), `LocalVar` (by index), `ClassStatic`, `Constant`
 *    (by type name, then by value), other bases (by text). Accessor order: `Static` (by type name),
 *    `Field` (by class name, field name, field type), `Array`.
 * 3. `AliasAllocInfo`: by the instruction index.
 */
object AliasInfoOrder : Comparator<AliasInfo> {
    override fun compare(a: AliasInfo, b: AliasInfo): Int = when (a) {
        is AliasApInfo -> when (b) {
            is AliasApInfo -> compareAp(a, b)
            is AliasAllocInfo -> -1
        }

        is AliasAllocInfo -> when (b) {
            is AliasApInfo -> 1
            is AliasAllocInfo -> a.allocInst.compareTo(b.allocInst)
        }
    }

    private fun compareAp(a: AliasApInfo, b: AliasApInfo): Int {
        val base = compareBase(a.base, b.base)
        if (base != 0) return base
        val size = a.accessors.size.compareTo(b.accessors.size)
        if (size != 0) return size
        for (i in a.accessors.indices) {
            val c = compareAccessor(a.accessors[i], b.accessors[i])
            if (c != 0) return c
        }
        return 0
    }

    private fun baseRank(b: AccessPathBase): Int = when (b) {
        AccessPathBase.This -> 0
        is AccessPathBase.Argument -> 1
        is AccessPathBase.LocalVar -> 2
        AccessPathBase.ClassStatic -> 3
        is AccessPathBase.Constant -> 4
        else -> 5
    }

    private fun compareBase(a: AccessPathBase, b: AccessPathBase): Int {
        val rank = baseRank(a).compareTo(baseRank(b))
        if (rank != 0) return rank
        return when {
            a is AccessPathBase.Argument && b is AccessPathBase.Argument -> a.idx.compareTo(b.idx)
            a is AccessPathBase.LocalVar && b is AccessPathBase.LocalVar -> a.idx.compareTo(b.idx)
            a is AccessPathBase.Constant && b is AccessPathBase.Constant ->
                compareValuesBy(a, b, { it.typeName }, { it.value })
            else -> a.toString().compareTo(b.toString())
        }
    }

    private fun accessorRank(a: AliasAccessor): Int = when (a) {
        is AliasAccessor.Static -> 0
        is AliasAccessor.Field -> 1
        AliasAccessor.Array -> 2
    }

    private fun compareAccessor(a: AliasAccessor, b: AliasAccessor): Int {
        val rank = accessorRank(a).compareTo(accessorRank(b))
        if (rank != 0) return rank
        return when {
            a is AliasAccessor.Static && b is AliasAccessor.Static -> a.typeName.compareTo(b.typeName)
            a is AliasAccessor.Field && b is AliasAccessor.Field ->
                compareValuesBy(a, b, { it.className }, { it.fieldName }, { it.fieldType })
            else -> 0
        }
    }
}
