package org.opentaint.dataflow.ap.ifds.markset

import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.RuleConditionRewriter
import org.opentaint.dataflow.taint.TaintMarkAwareConditionExpr
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

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
 * @property sites parallel to [MarkSetProgram.sites].
 * @property markNames mark id -> name.
 * @property coveredStatements every statement at which the prescan queried a
 *   rule (§4, "recorded statements"); used by the provider's fallback.
 */
class MarkSetInput(
    val program: MarkSetProgram,
    val sites: List<SiteRef>,
    val markNames: List<String>,
    val coveredStatements: Set<CommonInst>,
)

/**
 * Language-agnostic recorder for the mark-set prescan (spec §4). Builds a
 * [MarkSetProgram] from the engine's call graph and rule residuals while the
 * prescan runs. Every `record*` method is a no-op unless [active], and all of
 * them are safe to call concurrently (the prescan calls this recorder from
 * multiple coroutine workers).
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

    private val lock = Any()

    // Interning tables, all guarded by [lock].
    private val methodIds = HashMap<CommonMethod, Int>()
    private val markIds = HashMap<String, Int>()
    private val markNames = ArrayList<String>()
    private val literalIds = HashMap<LiteralKey, Int>()

    // Edges, guarded by [lock]: dedup set plus an insertion-ordered adjacency source.
    private val edgeKeys = HashSet<Long>()
    private val edgeList = ArrayList<LongArray>() // each entry: [callerId, calleeId]

    // Sites, guarded by [lock]: M8 dedup on (statement, rule, MarkCond).
    private val siteDedup = HashMap<SiteDedupKey, Int>()
    private val siteEntries = ArrayList<MarkSite>()
    private val siteRefs = ArrayList<SiteRef>()

    private val coveredStatements = HashSet<CommonInst>()
    private val cleanerAtoms = BitSet()

    /** `(position, mark name, anyAccessor)`: the literal-id key (spec §4.1). */
    private data class LiteralKey(val position: PositionAccess, val markName: String, val anyAccessor: Boolean)

    /** The M8 dedup key: one site per `(statement, rule, MarkCond)`. */
    private data class SiteDedupKey(
        val statement: CommonInst,
        val rule: CommonTaintConfigurationItem,
        val cond: MarkCond,
    )

    /** Records a call edge `caller --call--> callee`, while the phase is Prescan. */
    fun recordEdge(caller: CommonMethod, call: CommonInst, callee: CommonMethod) {
        if (!active || overflow) return
        synchronized(lock) {
            if (!active || overflow) return
            val callerId = internMethod(caller)
            val calleeId = internMethod(callee)
            val key = edgeKey(callerId, calleeId)
            if (edgeKeys.contains(key)) return
            if (edgeList.size >= maxEdges) {
                overflow = true
                return
            }
            edgeKeys.add(key)
            edgeList.add(longArrayOf(callerId.toLong(), calleeId.toLong()))
        }
    }

    /** Records a statement at which the prescan queried any rule (§4, provider fallback). */
    fun recordStatement(statement: CommonInst) {
        if (!active || overflow) return
        synchronized(lock) {
            if (!active || overflow) return
            coveredStatements.add(statement)
        }
    }

    /**
     * Records one rule site. Deduplicated on `(statement, rule, MarkCond)` (M8); if the
     * same rule gets different residuals at the same statement, all of them are kept.
     * A `false` residual is not recorded.
     */
    fun recordSite(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        kind: SiteKind,
        residual: RuleConditionRewriter.ExprOrConstant,
        gens: List<String>,
    ) {
        if (!active || overflow) return
        synchronized(lock) {
            if (!active || overflow) return
            val cond = residual.toMarkCondOrNull() ?: return
            val key = SiteDedupKey(statement, rule, cond)
            if (siteDedup.containsKey(key)) return
            if (siteEntries.size >= maxSites) {
                overflow = true
                return
            }
            val methodId = internMethod(statement.location.method)
            val genIds = IntArray(gens.size) { internMark(gens[it]) }
            siteDedup[key] = siteEntries.size
            siteEntries.add(MarkSite(methodId, kind, cond, genIds))
            siteRefs.add(SiteRef(statement, rule, gens))
        }
    }

    /** Adds the positive atoms of a cleaner's residual to `Program.cleanerAtoms` (spec §6.3 (4)). */
    fun recordCleaner(statement: CommonInst, residual: RuleConditionRewriter.ExprOrConstant) {
        if (!active || overflow) return
        synchronized(lock) {
            if (!active || overflow) return
            val cond = residual.toMarkCondOrNull() ?: return
            cond.atoms(cleanerAtoms)
        }
    }

    /** Builds the [MarkSetInput] recorded so far. Safe to call once the prescan is done. */
    fun seal(roots: Collection<CommonMethod>): MarkSetInput {
        synchronized(lock) {
            val methodCount = methodIds.size

            val outDegree = IntArray(methodCount)
            for (edge in edgeList) outDegree[edge[0].toInt()]++
            val callees = Array(methodCount) { IntArray(outDegree[it]) }
            val cursor = IntArray(methodCount)
            for (edge in edgeList) {
                val callerId = edge[0].toInt()
                callees[callerId][cursor[callerId]++] = edge[1].toInt()
            }

            val rootIds = roots.mapNotNull { methodIds[it] }.distinct().toIntArray()

            // E0 (PcWF): every site's method is a node. Holds by construction (methodId
            // came from `internMethod`, which never returns an id >= methodIds.size); assert it.
            for (site in siteEntries) {
                check(site.method in 0 until methodCount) {
                    "PcWF violated (E0): site method ${site.method} is not a recorded node"
                }
            }

            val program = MarkSetProgram(
                methodCount = methodCount,
                markCount = markNames.size,
                roots = rootIds,
                callees = callees,
                sites = siteEntries.toList(),
                cleanerAtoms = cleanerAtoms.clone() as BitSet,
            )
            return MarkSetInput(
                program = program,
                sites = siteRefs.toList(),
                markNames = markNames.toList(),
                coveredStatements = coveredStatements.toSet(),
            )
        }
    }

    // ---- helpers, all called with [lock] held ------------------------------

    private fun internMethod(method: CommonMethod): Int = methodIds.getOrPut(method) { methodIds.size }

    private fun internMark(name: String): Int = markIds.getOrPut(name) {
        val id = markNames.size
        markNames.add(name)
        id
    }

    private fun edgeKey(callerId: Int, calleeId: Int): Long =
        (callerId.toLong() shl 32) or (calleeId.toLong() and 0xFFFFFFFFL)

    /** `isTrue` -> `True`; `isFalse` -> `null` (not recorded); else the expr's `MarkCond`. */
    private fun RuleConditionRewriter.ExprOrConstant.toMarkCondOrNull(): MarkCond? = when {
        isFalse -> null
        isTrue -> MarkCond.True
        else -> expr.toMarkCond()
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
        val literalId = literalIds.getOrPut(LiteralKey(position, mark.mark, anyAccessor)) { literalIds.size }
        return MarkCond.Lit(markId, literalId)
    }
}
