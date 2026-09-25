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
 */
class MarkSetProgram(
    val methodCount: Int,
    val markCount: Int,
    val roots: IntArray,
    val callees: Array<IntArray>,
    val sites: List<MarkSite>,
    val cleanerAtoms: BitSet,
)

/**
 * @property relaxed option 4* (spec §6.2): a joined cube is tested by "some atom is in `U`".
 * @property relevance compute `Needed` (spec §6.3); when off, every mark is needed.
 */
data class MarkSetOptions(val relaxed: Boolean = false, val relevance: Boolean = true)

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
) {
    override fun toString(): String =
        "MarkSetStats(methods=$methods, edges=$edges, sites=$sites, signatures=$signatures, " +
            "distinctRootSets=$distinctRootSets, outerRounds=$outerRounds, applicableSites=$applicableSites, " +
            "applicableSinks=$applicableSinks, neededMarks=$neededMarks)"
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
