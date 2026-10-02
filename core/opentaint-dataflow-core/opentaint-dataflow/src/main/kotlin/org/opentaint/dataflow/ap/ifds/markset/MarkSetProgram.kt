package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet

enum class SiteKind { SOURCE, SINK, PASS_THROUGH }

/**
 * One recorded rule site (spec §4): a rule instance at a statement of [method],
 * with its mark-only residual [cond] and the marks [gens] of its `AssignMark`
 * actions (for a sink: its `trackFactsReachAnalysisEnd` marks).
 */
class MarkSite(val method: Int, val kind: SiteKind, val cond: MarkCond, val gens: IntArray)

/**
 * The mark-set program (spec §4; `Program` in `MarkScan/Basic.lean`), with
 * nodes = methods. Methods and marks are dense ints.
 *
 * @property roots root method ids.
 * @property callees for every method, its distinct callee methods.
 * @property cleanerAtoms the positive mark atoms of every recorded cleaner residual (spec §6.3 (4)).
 * @property cfg the engine CFG of every method, for option 3* (spec §9); `null` when not recorded.
 */
class MarkSetProgram(
    val methodCount: Int,
    val markCount: Int,
    val roots: IntArray,
    val callees: Array<IntArray>,
    val sites: List<MarkSite>,
    val cleanerAtoms: BitSet,
    val cfg: MethodCfg? = null,
)

/**
 * The statement-level graph of every method of a [MarkSetProgram], for option 3* (spec §9;
 * `Program.pcs`/`succ`/`exits`/`calls` in `MarkScan/Basic.lean`). The statements of method `m`
 * are `0 until stmtCount[m]`.
 *
 * @property succ `succ[m][s]`: the successors of statement `s` of `m` (the engine's normal edges).
 * @property entry the entry statement of every method (Lean pc `0`).
 * @property exits the exit statements of every method.
 * @property siteStmt `siteStmt[i]`: the statement of site `i` ([MarkSetProgram.sites]) in its method.
 * @property callsAt `callsAt[m][s]`: the callees of the call at statement `s` of `m`.
 */
class MethodCfg(
    val stmtCount: IntArray,
    val succ: Array<Array<IntArray>>,
    val entry: IntArray,
    val exits: Array<IntArray>,
    val siteStmt: IntArray,
    val callsAt: Array<Array<IntArray>>,
)

/**
 * @property relaxed option 4* (spec §6.2): a joined cube is tested by "some atom is in `U`".
 * @property relevance compute `Needed` (spec §6.3); when off, every mark is needed.
 */
data class MarkSetOptions(val relaxed: Boolean = false, val relevance: Boolean = true)

/** @property rootPoints option 3* only: the `(root, statement)` pairs the scan visited, over every round. */
class MarkSetStats(
    val methods: Int,
    val edges: Int,
    val sites: Int,
    val signatures: Int,
    val distinctRootSets: Int,
    val outerRounds: Int,
    val applicableSites: Int,
    val applicableSinks: Int,
    val neededMarks: Int,
    val rootPoints: Long = 0L,
) {
    override fun toString(): String =
        "MarkSetStats(methods=$methods, edges=$edges, sites=$sites, signatures=$signatures, " +
            "distinctRootSets=$distinctRootSets, outerRounds=$outerRounds, applicableSites=$applicableSites, " +
            "applicableSinks=$applicableSinks, neededMarks=$neededMarks, rootPoints=$rootPoints)"
}

/**
 * @property applicable indices into [MarkSetProgram.sites] of the applicable sites.
 * @property needed the needed marks; every mark when relevance is off.
 * @property rootMarks `S_E` for every root `E` (used by tests).
 */
class MarkSetResult(
    val applicable: BitSet,
    val needed: BitSet,
    val rootMarks: Map<Int, BitSet>,
    val stats: MarkSetStats,
)
