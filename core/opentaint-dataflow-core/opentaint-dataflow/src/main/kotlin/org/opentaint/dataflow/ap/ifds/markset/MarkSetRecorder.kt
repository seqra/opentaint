package org.opentaint.dataflow.ap.ifds.markset

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
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
import java.util.concurrent.atomic.AtomicLong

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
 * One failed debug check (spec §7): [check] is `"E1"` (a full-scan call or entry point the prescan
 * did not create) or `"E2"` (a full-scan rule residual at a covered statement the prescan did not
 * record); [detail] names the statement, the rule or edge, and the residual.
 */
data class CoverageViolation(val check: String, val detail: String)

/**
 * The result of [MarkSetRecorder.checkCoverage].
 *
 * @property violations every E1 and E2 violation; empty when the prescan covered the full scan.
 * @property observedCalls the distinct `(caller, call statement, callee)` the full scan resolved.
 * @property observedSites the distinct rule residuals the full scan evaluated, over every statement.
 * @property uncoveredSites the part of [observedSites] at statements the prescan never queried a
 *   rule at. E2 does not cover them: the provider falls back to the delegate there (spec §10).
 */
class MarkSetCoverage(
    val violations: List<CoverageViolation>,
    val observedCalls: Int,
    val observedSites: Int,
    val uncoveredSites: Int,
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
 * @property maxEdges cap on the number of distinct recorded call edges, and separately on the
 *   number of distinct recorded call points. Exceeding it sets [overflow] and stops recording.
 * @property maxBytes cap on [estimatedBytes], the recorder's estimated retained size (spec §6.6,
 *   trigger 3: 512 MB by default). Exceeding it sets [overflow] and stops recording.
 * @property recordCalls also record every call point `(caller, call statement, callee)`, which
 *   option 3* needs (spec §9); off otherwise, so the default mode pays nothing for it.
 * @property debugChecks the E1/E2 debug checks (spec §7): the prescan also records its
 *   `(call statement, callee)` pairs and its method entry points, and after [startObserving] the
 *   full scan's calls, entry points and rule residuals are observed, for [checkCoverage]. Off
 *   otherwise, so the default mode pays nothing for it.
 */
class MarkSetRecorder(
    val maxSites: Int = 20_000_000,
    val maxEdges: Int = 20_000_000,
    val maxBytes: Long = DEFAULT_MAX_BYTES,
    val recordCalls: Boolean = false,
    val debugChecks: Boolean = false,
) {
    /** True only while the prescan phase is active; set by the caller. */
    @Volatile
    var active: Boolean = false

    /** Set once a cap ([maxSites], [maxEdges] or [maxBytes]) is exceeded; recording then stops. */
    @Volatile
    var overflow: Boolean = false

    private val bytes = AtomicLong()

    /**
     * The recorder's estimated retained size: every new entry of a recording table is charged a
     * constant ([INTERNED_BYTES], [COND_BYTES], [SITE_ENTRY_BYTES], [SITE_BYTES], [EDGE_BYTES],
     * [CALL_POINT_BYTES], [STATEMENT_BYTES], [CLEANER_BYTES]) once. The debug-check observation
     * sets are not charged (only the residual memo they share with recording is): the cap matters
     * only while the prescan records, since the mark-set phase reads [overflow] right after it.
     */
    val estimatedBytes: Long get() = bytes.get()

    /** With [debugChecks] only: true from [startObserving] (the full scan) until [checkCoverage]. */
    @Volatile
    var observing: Boolean = false
        private set

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

    /** Call points, with [recordCalls] only. */
    private var callPoints = ConcurrentHashMap.newKeySet<CallPoint>()
    private val callPointCount = AtomicInteger()

    /** One entry per `(statement, rule)`, mapped to itself (the entry is its own key). */
    private var siteEntries = ConcurrentHashMap<SiteEntry, SiteEntry>()
    private val siteCount = AtomicInteger()

    private var coveredStatements = ConcurrentHashMap.newKeySet<CommonInst>()

    // Cleaners: `(statement, residual)` already recorded, and the atoms, guarded by [cleanerAtoms].
    private var cleanerSeen = ConcurrentHashMap.newKeySet<CleanerKey>()
    private val cleanerAtoms = BitSet()

    // Debug checks (E1): what the prescan created. Empty unless [debugChecks].
    private var prescanCalls = ConcurrentHashMap.newKeySet<CallSite>()
    private var prescanEntryPoints = ConcurrentHashMap.newKeySet<MethodEntryPoint>()

    // Debug checks: what the full scan did, while [observing].
    private var observedCalls = ConcurrentHashMap.newKeySet<ObservedCall>()
    private var observedEntryPoints = ConcurrentHashMap.newKeySet<MethodEntryPoint>()
    private var observedSites = ConcurrentHashMap.newKeySet<ObservedSite>()
    private var observedCleaners = ConcurrentHashMap.newKeySet<CleanerKey>()
    private var unobservable = ConcurrentHashMap.newKeySet<String>()

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

    private data class CallPoint(val caller: Int, val statement: CommonInst, val callee: Int)

    /** E1's key: a call statement resolved to a callee. */
    private data class CallSite(val statement: CommonInst, val callee: CommonMethod)

    private data class ObservedCall(val caller: CommonMethod, val statement: CommonInst, val callee: CommonMethod)

    private data class ObservedSite(
        val statement: CommonInst,
        val rule: CommonTaintConfigurationItem,
        val kind: SiteKind,
        val residual: Any,
        val cond: MarkCond,
    )

    /**
     * Records a call edge `caller --call--> callee`, while the phase is Prescan. With [recordCalls],
     * also records the call point.
     */
    fun recordEdge(caller: CommonMethod, call: CommonInst, callee: CommonMethod) {
        if (!active || overflow) return
        val callerId = internMethod(caller)
        val calleeId = internMethod(callee)
        if (debugChecks && prescanCalls.add(CallSite(call, callee))) charge(CALL_POINT_BYTES)
        if (recordCalls) recordCallPoint(CallPoint(callerId, call, calleeId))
        val key = edgeKey(callerId, calleeId)
        if (key in edgeKeys || !edgeKeys.add(key)) return
        if (edgeCount.incrementAndGet() > maxEdges || !charge(EDGE_BYTES)) {
            overflow = true
            return
        }
        edgeList.add(key)
    }

    private fun recordCallPoint(point: CallPoint) {
        if (point in callPoints || !callPoints.add(point)) return
        if (callPointCount.incrementAndGet() > maxEdges) overflow = true
        charge(CALL_POINT_BYTES)
    }

    /** Records a statement at which the prescan queried any rule (§4, provider fallback). */
    fun recordStatement(statement: CommonInst) {
        if (!active || overflow) return
        if (statement in coveredStatements) return
        if (coveredStatements.add(statement)) charge(STATEMENT_BYTES)
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
            if (siteCount.incrementAndGet() > maxSites || !charge(SITE_BYTES)) {
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
        return siteEntries.putIfAbsent(probe, probe) ?: probe.also { charge(SITE_ENTRY_BYTES) }
    }

    /** Adds the positive atoms of a cleaner's residual to `Program.cleanerAtoms` (spec §6.3 (4)). */
    fun recordCleaner(statement: CommonInst, residual: RuleConditionRewriter.ExprOrConstant) {
        if (!active || overflow) return
        if (residual.isFalse || !residual.hasPositiveLiteral()) return
        val key = CleanerKey(statement, residual.key())
        if (key in cleanerSeen || !cleanerSeen.add(key)) return
        charge(CLEANER_BYTES)
        val atoms = markCondOf(residual).atoms()
        synchronized(cleanerAtoms) { cleanerAtoms.or(atoms) }
    }

    /**
     * Debug checks (E1): records a method entry point the engine just created. The prescan's are
     * kept; one created while [observing] (the full scan) is checked against them. A no-op without
     * [debugChecks].
     */
    fun recordEntryPoint(entryPoint: MethodEntryPoint) {
        if (!debugChecks) return
        if (observing) {
            observedEntryPoints.add(entryPoint)
        } else if (active && !overflow) {
            if (prescanEntryPoints.add(entryPoint)) charge(STATEMENT_BYTES)
        }
    }

    /**
     * Debug checks (E1): observes a call the full scan resolved, on any edge kind. A no-op unless
     * [observing].
     */
    fun observeCall(caller: CommonMethod, call: CommonInst, callee: CommonMethod) {
        if (!observing) return
        observedCalls.add(ObservedCall(caller, call, callee))
    }

    /**
     * Debug checks (E2): observes one rule residual the full scan evaluated, before the selection
     * filters it. Skipped as [recordSite] skips it: a `false` residual, and a pass-through
     * residual without a positive mark literal. A no-op unless [observing].
     */
    fun observeSite(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        kind: SiteKind,
        residual: RuleConditionRewriter.ExprOrConstant,
    ) {
        if (!observing) return
        if (residual.isFalse) return
        if (kind == SiteKind.PASS_THROUGH && !residual.hasPositiveLiteral()) return
        observedSites.add(ObservedSite(statement, rule, kind, residual.key(), markCondOf(residual)))
    }

    /**
     * Debug checks (E2): observes a cleaner residual the full scan evaluated. Skipped as
     * [recordCleaner] skips it: without a positive mark literal. A no-op unless [observing].
     */
    fun observeCleaner(statement: CommonInst, residual: RuleConditionRewriter.ExprOrConstant) {
        if (!observing) return
        if (residual.isFalse || !residual.hasPositiveLiteral()) return
        observedCleaners.add(CleanerKey(statement, residual.key()))
    }

    /**
     * Debug checks (E2): the full scan's rule residuals cannot be observed, for [reason] (e.g. the
     * unrestricted rules are unavailable), so E2 would pass vacuously. [checkCoverage] reports it as
     * one E2 violation per distinct reason. A no-op unless [observing].
     */
    fun observeUnavailable(reason: String) {
        if (!observing) return
        unobservable.add(reason)
    }

    /**
     * Debug checks: stops recording and starts observing the full scan. Call it after [seal],
     * instead of [release], so that the prescan's tables stay for [checkCoverage].
     */
    fun startObserving() {
        check(debugChecks) { "observing needs debugChecks" }
        active = false
        observing = true
    }

    /**
     * Debug checks: stops observing, and returns every full-scan observation the prescan did not
     * cover (spec §7):
     * - E1: a `(call statement, callee)` or a method entry point the prescan did not create;
     * - E2: a rule residual at a covered statement not recorded there for that rule, and each
     *   [observeUnavailable] reason. Uncovered statements fall back to the delegate and are only
     *   counted.
     *
     * Call it once the full scan is done (no concurrent `observe*` calls).
     */
    fun checkCoverage(): MarkSetCoverage {
        observing = false
        val violations = ArrayList<CoverageViolation>()

        for (call in observedCalls) {
            if (CallSite(call.statement, call.callee) in prescanCalls) continue
            violations += CoverageViolation(
                "E1", "call ${call.caller} -> ${call.callee} at ${call.statement} was not resolved by the prescan"
            )
        }
        for (entryPoint in observedEntryPoints) {
            if (entryPoint in prescanEntryPoints) continue
            violations += CoverageViolation(
                "E1", "entry point $entryPoint at ${entryPoint.statement} was not created by the prescan"
            )
        }

        var uncovered = 0
        for (site in observedSites) {
            if (site.statement !in coveredStatements) {
                uncovered++
                continue
            }
            val entry = siteEntries[SiteEntry(site.statement, site.rule, site.kind)]
            if (entry != null && site.cond in entry.conds) continue
            val recorded = entry?.conds?.toList() ?: "nothing"
            violations += CoverageViolation(
                "E2", "${site.kind} ${site.rule} at ${site.statement} (${site.statement.location.method}) " +
                    "with residual ${site.residual.show()} (${site.cond}); the prescan recorded $recorded"
            )
        }
        for (cleaner in observedCleaners) {
            if (cleaner.statement !in coveredStatements) {
                uncovered++
                continue
            }
            if (cleaner in cleanerSeen) continue
            violations += CoverageViolation(
                "E2", "cleaner at ${cleaner.statement} (${cleaner.statement.location.method}) " +
                    "with residual ${cleaner.residual.show()} was not recorded by the prescan"
            )
        }

        for (reason in unobservable) {
            violations += CoverageViolation("E2", "the full scan's rule residuals cannot be observed: $reason")
        }

        return MarkSetCoverage(
            violations = violations,
            observedCalls = observedCalls.size,
            observedSites = observedSites.size + observedCleaners.size,
            uncoveredSites = uncovered,
        )
    }

    /**
     * Builds the [MarkSetInput] recorded so far. Call it once the prescan is done and
     * recording has stopped (no concurrent `record*` calls).
     *
     * With [cfgSource], the program also gets its statement graph ([MarkSetProgram.cfg], option 3*),
     * built from the recorded call points (which need [recordCalls]). A method with other than one
     * entry statement gets one synthetic entry statement, after its own, leading to all of them.
     *
     * @throws MethodCfgUnavailable when a site or call statement is not a statement of its method's graph.
     */
    fun seal(roots: Collection<CommonMethod>, cfgSource: MethodCfgSource? = null): MarkSetInput {
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
        val methodArray = arrayOfNulls<CommonMethod>(methodCount)
        for ((method, id) in methodIds) methodArray[id] = method
        val methods = methodArray.map { checkNotNull(it) }

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
            cfg = cfgSource?.let { buildCfg(it, methods, sites, refs) },
        )
        return MarkSetInput(
            program = program,
            sites = refs,
            markNames = markNames.map { checkNotNull(it) },
            methods = methods,
            coveredStatements = HashSet(coveredStatements),
        )
    }

    /**
     * Drops every recorded table and observation and stops recording and observing, so that
     * nothing recorded survives into the full scan (with [debugChecks], past [checkCoverage]).
     * After this the recorder is empty and inactive.
     */
    fun release() {
        active = false
        observing = false
        methodIds = ConcurrentHashMap()
        markIds = ConcurrentHashMap()
        literalIds = ConcurrentHashMap()
        condCache = ConcurrentHashMap()
        gensCache = ConcurrentHashMap()
        edgeKeys = ConcurrentHashMap.newKeySet()
        edgeList = ConcurrentLinkedQueue()
        callPoints = ConcurrentHashMap.newKeySet()
        siteEntries = ConcurrentHashMap()
        coveredStatements = ConcurrentHashMap.newKeySet()
        cleanerSeen = ConcurrentHashMap.newKeySet()
        prescanCalls = ConcurrentHashMap.newKeySet()
        prescanEntryPoints = ConcurrentHashMap.newKeySet()
        observedCalls = ConcurrentHashMap.newKeySet()
        observedEntryPoints = ConcurrentHashMap.newKeySet()
        observedSites = ConcurrentHashMap.newKeySet()
        observedCleaners = ConcurrentHashMap.newKeySet()
        unobservable = ConcurrentHashMap.newKeySet()
        synchronized(cleanerAtoms) { cleanerAtoms.clear() }
        methodCount.set(0)
        markCount.set(0)
        literalCount.set(0)
        edgeCount.set(0)
        callPointCount.set(0)
        siteCount.set(0)
        bytes.set(0)
    }

    // ---- helpers -------------------------------------------------------------

    private fun buildCfg(
        source: MethodCfgSource,
        methods: List<CommonMethod>,
        sites: List<MarkSite>,
        refs: List<SiteRef>,
    ): MethodCfg {
        val n = methods.size
        val stmtCount = IntArray(n)
        val entry = IntArray(n)
        val exits = arrayOfNulls<IntArray>(n)
        val succ = arrayOfNulls<Array<IntArray>>(n)
        for (m in 0 until n) {
            val graph = source.graphOf(methods[m])
            exits[m] = graph.exits
            if (graph.entries.size == 1) {
                stmtCount[m] = graph.stmtCount
                entry[m] = graph.entries[0]
                succ[m] = graph.succ
            } else {
                stmtCount[m] = graph.stmtCount + 1
                entry[m] = graph.stmtCount
                succ[m] = graph.succ + graph.entries
            }
        }

        fun indexIn(method: Int, statement: CommonInst): Int {
            val index = source.indexOf(statement)
            if (statement.location.method != methods[method] || index !in 0 until stmtCount[method]) {
                throw MethodCfgUnavailable("statement $statement is not in the graph of ${methods[method]}")
            }
            return index
        }

        val siteStmt = IntArray(sites.size) { indexIn(sites[it].method, refs[it].statement) }

        val calls = Array(n) { m -> arrayOfNulls<IntArray>(stmtCount[m]) }
        for (point in callPoints) {
            val s = indexIn(point.caller, point.statement)
            val current = calls[point.caller][s] ?: NO_CALLEES
            if (point.callee !in current) calls[point.caller][s] = current + point.callee
        }

        return MethodCfg(
            stmtCount = stmtCount,
            succ = Array(n) { checkNotNull(succ[it]) },
            entry = entry,
            exits = Array(n) { checkNotNull(exits[it]) },
            siteStmt = siteStmt,
            callsAt = Array(n) { m -> Array(stmtCount[m]) { s -> calls[m][s] ?: NO_CALLEES } },
        )
    }

    /**
     * Adds [cost] to [estimatedBytes]; sets [overflow] and returns `false` once it exceeds [maxBytes].
     * Charged by whoever added the entry, so each entry is charged once.
     */
    private fun charge(cost: Long): Boolean {
        if (bytes.addAndGet(cost) <= maxBytes) return true
        overflow = true
        return false
    }

    private fun internMethod(method: CommonMethod): Int =
        methodIds[method] ?: methodIds.computeIfAbsent(method) {
            charge(INTERNED_BYTES)
            methodCount.getAndIncrement()
        }

    private fun internMark(name: String): Int =
        markIds[name] ?: markIds.computeIfAbsent(name) {
            charge(INTERNED_BYTES)
            markCount.getAndIncrement()
        }

    private fun internLiteral(key: LiteralKey): Int =
        literalIds[key] ?: literalIds.computeIfAbsent(key) {
            charge(INTERNED_BYTES)
            literalCount.getAndIncrement()
        }

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
        return condCache.putIfAbsent(expr, cond) ?: cond.also { charge(COND_BYTES) }
    }

    private fun internGens(names: List<String>): Gens {
        gensCache[names]?.let { return it }
        val gens = Gens(names, IntArray(names.size) { internMark(names[it]) })
        return gensCache.putIfAbsent(names, gens) ?: gens.also { charge(INTERNED_BYTES) }
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

    companion object {
        /** The default [maxBytes]: 512 MB (spec §6.6, trigger 3). */
        const val DEFAULT_MAX_BYTES: Long = 512L * 1024 * 1024

        // The [estimatedBytes] charges: the retained size of one entry on a 64-bit JVM with
        // compressed oops, i.e. its objects plus the concurrent-map node (32 B) and table slot
        // (~8 B at load factor 0.75) that hold it. Estimates, not measurements: they are meant to
        // be within a small factor, so the cap stops a runaway recording, not a large one.

        /** An interned method, mark, literal or gen-mark list: map node, slot, boxed id, key share. */
        const val INTERNED_BYTES: Long = 64

        /** A distinct residual's [MarkCond] (a few `Lit`/`And`/`Or` nodes) and its memo entry. */
        const val COND_BYTES: Long = 160

        /** A `(statement, rule)` site entry: the entry (40 B), its map node and slot, the empty cond array. */
        const val SITE_ENTRY_BYTES: Long = 96

        /** One more cond of a site entry: the grown array's slot and the copy's header share. */
        const val SITE_BYTES: Long = 16

        /** A call edge: the boxed key in the dedup set (node, slot, `Long`) and in the ordered queue. */
        const val EDGE_BYTES: Long = 96

        /** A call point (option 3*) or a debug-check call site: the key object, its node and slot. */
        const val CALL_POINT_BYTES: Long = 72

        /** A covered statement or a debug-check entry point: the set node and slot. */
        const val STATEMENT_BYTES: Long = 48

        /** A recorded cleaner `(statement, residual)`: the key object, its node and slot. */
        const val CLEANER_BYTES: Long = 72

        private val TRUE_KEY = Any()

        /** A residual key ([key]) for a debug-check message. */
        private fun Any.show(): String = if (this === TRUE_KEY) "true" else toString()
        private val NO_CONDS = emptyArray<MarkCond>()
        private val NO_CALLEES = IntArray(0)

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
