package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.markset.MarkSetCoverage
import org.opentaint.ir.api.common.cfg.CommonInst

/**
 * One marked access path at one statement, comparable across two analysis runs (the E10 debug diff,
 * spec §7, §8 Layer 3): the statement as its method, index and text, the access path from the
 * fact's base to the mark, and the mark. The fact's context (its initial fact) and its exclusions
 * are left out: under `T-REL` a needed fact may be derived under another context in the restricted
 * run (spec §6.4), so the diff compares facts per statement over all contexts.
 */
data class MarkFactKey(val statement: String, val path: String, val mark: String)

/**
 * Every [MarkFactKey] of [statementFacts] (as [TaintAnalyzer.statementsWithFacts] returns them): each
 * fact is walked from its base along every accessor path to a [TaintMarkAccessor]. A fact with no
 * mark (an abstract fact, whose marks live in the caller) contributes nothing.
 */
fun markFactKeys(statementFacts: Map<CommonInst, Set<FinalFactAp>>): Set<MarkFactKey> {
    val keys = hashSetOf<MarkFactKey>()
    for ((statement, facts) in statementFacts) {
        val stmt = "${statement.location.method}#${statement.location.index}: $statement"
        for (fact in facts) {
            val paths = mutableListOf<Pair<String, String>>()
            fact.filterFact(MarkPathCollector(fact.base.toString(), depth = 0, paths))
            paths.mapTo(keys) { (path, mark) -> MarkFactKey(stmt, path, mark) }
        }
    }
    return keys
}

/**
 * Collects `(path, mark)` for every path to a mark, by walking [FinalFactAp.filterFact]: each
 * accessor is checked once per path prefix, and the walk rejects at a mark, at the final accessor,
 * and past [MAX_DEPTH] accessors.
 */
private class MarkPathCollector(
    private val prefix: String,
    private val depth: Int,
    private val out: MutableList<Pair<String, String>>,
) : FactTypeChecker.FactApFilter {
    override fun check(accessor: Accessor): FactTypeChecker.FilterResult = when {
        accessor is TaintMarkAccessor -> {
            out.add(prefix to accessor.mark)
            FactTypeChecker.FilterResult.Reject
        }

        accessor is FinalAccessor || depth >= MAX_DEPTH -> FactTypeChecker.FilterResult.Reject
        else -> FactTypeChecker.FilterResult.FilterNext(MarkPathCollector("$prefix.$accessor", depth + 1, out))
    }

    private companion object {
        const val MAX_DEPTH = 64
    }
}

/**
 * The E10 debug diff (spec §7, §8 Layer 3): throws an [AssertionError] naming the missing and extra
 * facts unless the baseline and the mark-set run have the same facts, per statement, of every
 * needed mark. [neededMarks] `null` means every mark (no relevance, or a fail-open run). [what]
 * names the analysis.
 */
fun assertSameNeededFacts(
    baseline: Set<MarkFactKey>,
    markSet: Set<MarkFactKey>,
    neededMarks: Set<String>?,
    what: String,
) {
    fun Set<MarkFactKey>.needed() = if (neededMarks == null) this else filterTo(hashSetOf()) { it.mark in neededMarks }

    val expected = baseline.needed()
    val actual = markSet.needed()
    if (expected == actual) return

    fun Set<MarkFactKey>.show() = sortedWith(compareBy({ it.statement }, { it.path }, { it.mark }))
        .joinToString("") { "\n    ${it.statement} | ${it.path} ![${it.mark}]" }
    throw AssertionError(
        "mark-set differs from the baseline in the needed-mark facts (E10) of $what, needed marks $neededMarks" +
            "\n  missing under mark-set:${(expected - actual).show()}" +
            "\n  extra under mark-set:${(actual - expected).show()}"
    )
}

/**
 * The mark-set debug checks of one differential pair (spec §7, §8 Layers 2 and 3): the mark-set
 * run, whose phase ended with [outcome], passed E1 and E2 ([coverage]) if it selected, and both
 * runs have the same facts of every needed mark per statement (E10). [what] names the analysis.
 */
fun assertMarkSetDebugChecks(
    baselineFacts: Set<MarkFactKey>,
    markSetFacts: Set<MarkFactKey>,
    outcome: MarkSetOutcome?,
    coverage: MarkSetCoverage?,
    what: String,
) {
    if (outcome is MarkSetOutcome.Selected) {
        assertNoCoverageViolations(coverage ?: throw AssertionError("the debug checks did not run for $what"), what)
    }
    assertSameNeededFacts(baselineFacts, markSetFacts, (outcome as? MarkSetOutcome.Selected)?.neededMarks, what)
}

/**
 * The E1/E2 debug checks (spec §7): throws an [AssertionError] listing the violations unless
 * [coverage] has none. [what] names the analysis.
 */
fun assertNoCoverageViolations(coverage: MarkSetCoverage, what: String) {
    if (coverage.violations.isEmpty()) return
    throw AssertionError(
        "mark-set prescan does not cover the full scan of $what (${coverage.violations.size} violations):" +
            coverage.violations.joinToString("") { "\n  ${it.check}: ${it.detail}" }
    )
}
