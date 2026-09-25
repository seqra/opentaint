package org.opentaint.dataflow.ap.ifds.markset

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.atomic.AtomicInteger

/**
 * One recorded rule site, still holding its IR objects (spec §4: "the ids
 * needed to build the output"). Parallel to [MarkSetProgram.sites] in the
 * sealed [MarkSetInput]; `sites[i]` is the [SiteRef] for `program.sites[i]`.
 */
class SiteRef(
    val statement: CommonInst,
    val rule: CommonTaintConfigurationItem,
    val genMarks: List<String>,
)

/**
 * The result of [MarkSetRecorder.seal]: the dense [MarkSetProgram] plus the
 * side tables needed to translate its output back to IR objects.
 *
 * @property sites parallel to [MarkSetProgram.sites]. The sites of one
 *   `(statement, rule)` are contiguous.
 * @property markNames mark id -> name.
 * @property methods method id -> method (the program's nodes).
 * @property coveredStatements every statement at which the prescan queried a
 *   rule (§4, "recorded statements"); used by the provider's fallback.
 */
class MarkSetInput(
    val program: MarkSetProgram,
    val sites: List<SiteRef>,
    val markNames: List<String>,
    val methods: List<CommonMethod>,
    val coveredStatements: Set<CommonInst>,
)

/**
 * Language-agnostic recorder for the mark-set prescan (spec §4). Builds a
 * [MarkSetProgram] from the engine's call graph and rule residuals while the
 * prescan runs. Every `record*` method is a no-op unless [active], and all of
 * them are safe to call concurrently (the prescan calls this recorder from
 * multiple coroutine workers).
 *
 * Recording takes no global lock, and it is shaped for the prescan's volume
 * (millions of sites, mostly repeats of a few residual shapes):
 * - interning uses concurrent maps with dense counters;
 * - a residual is converted to a [MarkCond] once per distinct residual, and
 *   equal residuals share one [MarkCond] instance;
 * - a site is one small per-`(statement, rule)` entry holding its distinct
 *   conds (the M8 dedup scope); the [MarkSite]/[SiteRef] objects are built only
 *   by [seal].
 *
 * Existing engine behaviour is unaffected: every new hook this recorder
 * requires is gated on a non-null recorder by the caller, and this class has
 * no side effect beyond its own state.
 *
 * @property maxSites cap on the number of distinct recorded sites (by the M8
 *   dedup key). Exceeding it sets [overflow] and stops recording.
 * @property maxEdges cap on the number of distinct recorded call edges.
 *   Exceeding it sets [overflow] and stops recording.
 */
class MarkSetRecorder(val maxSites: Int = 20_000_000, val maxEdges: Int = 20_000_000) {
    /** True only while the prescan phase is active; set by the caller. */
    @Volatile
    var active: Boolean = false

    /** Set once a cap ([maxSites] or [maxEdges]) is exceeded; recording then stops. */
    @Volatile
    var overflow: Boolean = false

    // Interning tables: ids are dense, assigned inside `computeIfAbsent` (at most once per key).
    private var methodIds = ConcurrentHashMap<CommonMethod, Int>()
    private val methodCount = AtomicInteger()
    private var markIds = ConcurrentHashMap<String, Int>()
    private val markCount = AtomicInteger()
    private var literalIds = ConcurrentHashMap<LiteralKey, Int>()
    private val literalCount = AtomicInteger()

    /** Residual (structurally) -> its [MarkCond]: the conversion memo. */
    private var condCache = ConcurrentHashMap<Any, MarkCond>()

    /** Gen-mark names (structurally) -> their interned [Gens]. */
    private var gensCache = ConcurrentHashMap<List<String>, Gens>()

    // Edges: dedup set plus an insertion-ordered list of the same keys.
    private var edgeKeys = ConcurrentHashMap.newKeySet<Long>()
    private val edgeCount = AtomicInteger()
    private var edgeList = ConcurrentLinkedQueue<Long>()

    /** One entry per `(statement, rule)`, mapped to itself (the entry is its own key). */
    private var siteEntries = ConcurrentHashMap<SiteEntry, SiteEntry>()
    private val siteCount = AtomicInteger()

    private var coveredStatements = ConcurrentHashMap.newKeySet<CommonInst>()

    // Cleaners: `(statement, residual)` already recorded, and the atoms, guarded by [cleanerAtoms].
    private var cleanerSeen = ConcurrentHashMap.newKeySet<CleanerKey>()
    private val cleanerAtoms = BitSet()

    /** `(position, mark name, anyAccessor)`: the literal-id key (spec §4.1). */
    private data class LiteralKey(val position: PositionAccess, val markName: String, val anyAccessor: Boolean)

    private class Gens(val names: List<String>, val ids: IntArray)

    /**
     * Every site of one rule at one statement: the M8 dedup scope. Equality is by
     * `(statement, rule)` only. [conds] holds the distinct conds recorded (almost always one);
     * it is read without a lock and replaced under this entry's monitor.
     */
    private class SiteEntry(
        val statement: CommonInst,
        val rule: CommonTaintConfigurationItem,
        val kind: SiteKind,
    ) {
        private val hash = statement.hashCode() * 31 + rule.hashCode()

        @Volatile
        var gens: Gens? = null

        @Volatile
        var conds: Array<MarkCond> = NO_CONDS

        override fun equals(other: Any?): Boolean =
            this === other || (other is SiteEntry && statement == other.statement && rule == other.rule)

        override fun hashCode(): Int = hash
    }

    private data class CleanerKey(val statement: CommonInst, val residual: Any)

    /** Records a call edge `caller --call--> callee`, while the phase is Prescan. */
    fun recordEdge(caller: CommonMethod, call: CommonInst, callee: CommonMethod) {
        if (!active || overflow) return
        val key = edgeKey(internMethod(caller), internMethod(callee))
        if (key in edgeKeys || !edgeKeys.add(key)) return
        if (edgeCount.incrementAndGet() > maxEdges) {
            overflow = true
            return
        }
        edgeList.add(key)
    }

    /** Records a statement at which the prescan queried any rule (§4, provider fallback). */
    fun recordStatement(statement: CommonInst) {
        if (!active || overflow) return
        if (statement in coveredStatements) return
        coveredStatements.add(statement)
    }

    /**
     * Records one rule site. Deduplicated on `(statement, rule, MarkCond)` (M8); if the
     * same rule gets different residuals at the same statement, all of them are kept.
     * A `false` residual is not recorded, nor is a pass-through residual without a
     * positive mark literal: such a site has no gens and no atoms, so it cannot change
     * the scan's result (a pass-through only contributes its atoms to `Needed`, E8).
     */
    fun recordSite(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        kind: SiteKind,
        residual: RuleConditionRewriter.ExprOrConstant,
        gens: List<String>,
    ) {
        if (!active || overflow) return
        if (residual.isFalse) return
        if (kind == SiteKind.PASS_THROUGH && !residual.hasPositiveLiteral()) return

        val cond = markCondOf(residual)
        val entry = entryOf(statement, rule, kind, gens)
        if (cond in entry.conds) return

        synchronized(entry) {
            val conds = entry.conds
            if (cond in conds) return
            if (siteCount.incrementAndGet() > maxSites) {
                overflow = true
                return
            }
            entry.conds = conds + cond
        }
    }

    private fun entryOf(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        kind: SiteKind,
        gens: List<String>,
    ): SiteEntry {
        val probe = SiteEntry(statement, rule, kind)
        siteEntries[probe]?.let { return it }
        probe.gens = internGens(gens)
        return siteEntries.putIfAbsent(probe, probe) ?: probe
    }

    /** Adds the positive atoms of a cleaner's residual to `Program.cleanerAtoms` (spec §6.3 (4)). */
    fun recordCleaner(statement: CommonInst, residual: RuleConditionRewriter.ExprOrConstant) {
        if (!active || overflow) return
        if (residual.isFalse || !residual.hasPositiveLiteral()) return
        val key = CleanerKey(statement, residual.key())
        if (key in cleanerSeen || !cleanerSeen.add(key)) return
        val atoms = markCondOf(residual).atoms()
        synchronized(cleanerAtoms) { cleanerAtoms.or(atoms) }
    }

    /**
     * Builds the [MarkSetInput] recorded so far. Call it once the prescan is done and
     * recording has stopped (no concurrent `record*` calls).
     */
    fun seal(roots: Collection<CommonMethod>): MarkSetInput {
        // Sites first: interning a site's method may add a node (E0).
        val sites = ArrayList<MarkSite>()
        val refs = ArrayList<SiteRef>()
        for (entry in siteEntries.keys) {
            val gens = checkNotNull(entry.gens)
            val methodId = internMethod(entry.statement.location.method)
            for (cond in entry.conds) {
                sites.add(MarkSite(methodId, entry.kind, cond, gens.ids))
                refs.add(SiteRef(entry.statement, entry.rule, gens.names))
            }
        }

        val methodCount = methodCount.get()
        val methods = arrayOfNulls<CommonMethod>(methodCount)
        for ((method, id) in methodIds) methods[id] = method

        val edges = edgeList.toList()
        val outDegree = IntArray(methodCount)
        for (edge in edges) outDegree[edgeCaller(edge)]++
        val callees = Array(methodCount) { IntArray(outDegree[it]) }
        val cursor = IntArray(methodCount)
        for (edge in edges) {
            val callerId = edgeCaller(edge)
            callees[callerId][cursor[callerId]++] = edgeCallee(edge)
        }

        val rootIds = roots.mapNotNull { methodIds[it] }.distinct().toIntArray()

        // E0 (PcWF): every site's method is a node. Holds by construction (methodId
        // came from `internMethod`, which never returns an id >= methodCount); assert it.
        for (site in sites) {
            check(site.method in 0 until methodCount) {
                "PcWF violated (E0): site method ${site.method} is not a recorded node"
            }
        }

        val markNames = arrayOfNulls<String>(markCount.get())
        for ((name, id) in markIds) markNames[id] = name

        val program = MarkSetProgram(
            methodCount = methodCount,
            markCount = markNames.size,
            roots = rootIds,
            callees = callees,
            sites = sites,
            cleanerAtoms = synchronized(cleanerAtoms) { cleanerAtoms.clone() as BitSet },
        )
        return MarkSetInput(
            program = program,
            sites = refs,
            markNames = markNames.map { checkNotNull(it) },
            methods = methods.map { checkNotNull(it) },
            coveredStatements = HashSet(coveredStatements),
        )
    }

    /**
     * Drops every recorded table and stops recording, so that nothing recorded survives
     * into the full scan. After this the recorder is empty and inactive.
     */
    fun release() {
        active = false
        methodIds = ConcurrentHashMap()
        markIds = ConcurrentHashMap()
        literalIds = ConcurrentHashMap()
        condCache = ConcurrentHashMap()
        gensCache = ConcurrentHashMap()
        edgeKeys = ConcurrentHashMap.newKeySet()
        edgeList = ConcurrentLinkedQueue()
        siteEntries = ConcurrentHashMap()
        coveredStatements = ConcurrentHashMap.newKeySet()
        cleanerSeen = ConcurrentHashMap.newKeySet()
        synchronized(cleanerAtoms) { cleanerAtoms.clear() }
        methodCount.set(0)
        markCount.set(0)
        literalCount.set(0)
        edgeCount.set(0)
        siteCount.set(0)
    }

    // ---- helpers -------------------------------------------------------------

    private fun internMethod(method: CommonMethod): Int =
        methodIds[method] ?: methodIds.computeIfAbsent(method) { methodCount.getAndIncrement() }

    private fun internMark(name: String): Int =
        markIds[name] ?: markIds.computeIfAbsent(name) { markCount.getAndIncrement() }

    private fun internLiteral(key: LiteralKey): Int =
        literalIds[key] ?: literalIds.computeIfAbsent(key) { literalCount.getAndIncrement() }

    private fun edgeKey(callerId: Int, calleeId: Int): Long =
        (callerId.toLong() shl 32) or (calleeId.toLong() and 0xFFFFFFFFL)

    private fun edgeCaller(key: Long): Int = (key ushr 32).toInt()
    private fun edgeCallee(key: Long): Int = key.toInt()

    /** The residual's structural identity: the expression, or a marker for `true`. */
    private fun RuleConditionRewriter.ExprOrConstant.key(): Any = if (isTrue) TRUE_KEY else expr

    /** `isTrue` -> `True`; otherwise the expr's `MarkCond`, converted once per distinct residual. */
    private fun markCondOf(residual: RuleConditionRewriter.ExprOrConstant): MarkCond {
        if (residual.isTrue) return MarkCond.True
        val expr = residual.expr
        condCache[expr]?.let { return it }
        val cond = expr.toMarkCond()
        return condCache.putIfAbsent(expr, cond) ?: cond
    }

    private fun internGens(names: List<String>): Gens {
        gensCache[names]?.let { return it }
        val gens = Gens(names, IntArray(names.size) { internMark(names[it]) })
        return gensCache.putIfAbsent(names, gens) ?: gens
    }

    private fun TaintMarkAwareConditionExpr.toMarkCond(): MarkCond = when (this) {
        is TaintMarkAwareConditionExpr.And -> MarkCond.And(args.map { it.toMarkCond() })
        is TaintMarkAwareConditionExpr.Or -> MarkCond.Or(args.map { it.toMarkCond() })
        is TaintMarkAwareConditionExpr.ContainsMarkLiteral ->
            literalToMarkCond(position, mark, negated, anyAccessor = false)
        is TaintMarkAwareConditionExpr.ContainsMarkOnAnyAccessorLiteral ->
            literalToMarkCond(position, mark, negated, anyAccessor = true)
    }

    /** Negated literals become `True` (E5); everything else becomes an interned [MarkCond.Lit]. */
    private fun literalToMarkCond(
        position: PositionAccess,
        mark: TaintMarkAccessor,
        negated: Boolean,
        anyAccessor: Boolean,
    ): MarkCond {
        if (negated) return MarkCond.True
        val markId = internMark(mark.mark)
        val literalId = internLiteral(LiteralKey(position, mark.mark, anyAccessor))
        return MarkCond.Lit(markId, literalId)
    }

    private companion object {
        private val TRUE_KEY = Any()
        private val NO_CONDS = emptyArray<MarkCond>()

        /** Whether the residual has a positive (non-negated) mark literal, i.e. a non-empty `atoms()`. */
        private fun RuleConditionRewriter.ExprOrConstant.hasPositiveLiteral(): Boolean =
            !isTrue && !isFalse && expr.hasPositiveLiteral()

        private fun TaintMarkAwareConditionExpr.hasPositiveLiteral(): Boolean = when (this) {
            is TaintMarkAwareConditionExpr.And -> args.any { it.hasPositiveLiteral() }
            is TaintMarkAwareConditionExpr.Or -> args.any { it.hasPositiveLiteral() }
            is TaintMarkAwareConditionExpr.Literal -> !negated
        }
    }
}
