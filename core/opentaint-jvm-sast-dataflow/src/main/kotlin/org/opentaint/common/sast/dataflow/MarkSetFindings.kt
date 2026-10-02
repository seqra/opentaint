package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.ir.api.common.cfg.CommonInst

/** A finding's key under the mark-set soundness contract (spec §2, E9): its sink rule and sink statement. */
typealias MarkSetFindingKey = Pair<String, CommonInst>

fun TaintSinkTracker.TaintVulnerability.markSetFindingKey(): MarkSetFindingKey = ruleId to statement

/**
 * One analysis run's findings as the mark-set differential gate compares them (spec §8 Layer 3):
 * the confirmed findings before the trace filter (the contract's comparison point, E9, observed
 * through [TaintAnalyzer.onConfirmedVulnerabilities]) and the reported findings after it.
 */
class MarkSetFindings(
    val confirmed: List<TaintSinkTracker.TaintVulnerability>,
    val reported: List<VulnerabilityWithTrace>,
)

/**
 * Throws an [AssertionError] naming the missing and extra keys unless [markSet] has the same
 * confirmed and the same reported finding keys as [baseline]. [what] names the analysis.
 */
fun assertSameMarkSetFindings(baseline: MarkSetFindings, markSet: MarkSetFindings, what: String) {
    assertSameKeys(
        baseline.confirmed.mapTo(hashSetOf()) { it.markSetFindingKey() },
        markSet.confirmed.mapTo(hashSetOf()) { it.markSetFindingKey() },
        "confirmed findings of $what",
    )
    assertSameKeys(
        baseline.reported.mapTo(hashSetOf()) { it.vulnerability.markSetFindingKey() },
        markSet.reported.mapTo(hashSetOf()) { it.vulnerability.markSetFindingKey() },
        "reported findings of $what",
    )
}

private fun assertSameKeys(baseline: Set<MarkSetFindingKey>, markSet: Set<MarkSetFindingKey>, what: String) {
    if (baseline == markSet) return

    fun Set<MarkSetFindingKey>.show() = map { (rule, stmt) -> "$rule @ ${stmt.location.method}: $stmt" }
    throw AssertionError(
        "mark-set differs from the baseline in the $what\n" +
            "  missing under mark-set: ${(baseline - markSet).show()}\n" +
            "  extra under mark-set: ${(markSet - baseline).show()}"
    )
}
