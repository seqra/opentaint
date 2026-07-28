package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

/**
 * A whole-object (`$*`) sanitizer inside a summarized wrapper must stay effective when the
 * wrapper ALSO has an unsanitized flow from the same initial fact.
 *
 * `wrap` copies its whole argument twice — once before the starred clean (`p.raw`) and once
 * after it (`p.val`). Both summary edges share the initial fact `b`, so the summary storage
 * merges their exclusion sets with `intersect`, which silently drops the sanitized edge's
 * [org.opentaint.dataflow.ap.ifds.DeepMarkExclusion] unless the edges are grouped by their
 * deep subset. The caller's whole-object mark (`b.[any].![m]`) is then re-admitted below
 * `p.val` and the sanitized read reports a false positive, while the unsanitized read
 * (`p.raw`) must of course stay reported.
 *
 * The Tree subclass exercises the storage grouping (red before the fix). The Automata
 * subclass exercises the same contract plus the cleaner-lineage continuation: the cleaned
 * fact enters the resolved `clean` via call-to-start and must re-emerge from its identity
 * summary — which requires the exit-point compatibility filter to keep fully abstract
 * final facts (see AccessGraphCompatibilityFilterTest; the base-only-clean case was red
 * before that fix).
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
abstract class DeepCleanSummaryAnalysisTest : AnalysisTest() {

    companion object {
        private const val TEST_CLS = "test.samples.DeepCleanSummarySample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "deep-clean-summary-rule"
    }

    override val sourceFileExtension: String = "java"

    override val analysisUnrollStrategy: AnyAccessorUnrollStrategy = object : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private fun wholeObjectEntryPoint(entryPointMethod: String) = SerializedRule.EntryPoint(
        function = functionMatcher(TEST_CLS, entryPointMethod),
        taint = listOf(
            SerializedTaintAssignAction(
                kind = TAINT_MARK,
                pos = PositionBaseWithModifiers.BaseOnly(Argument(0))
            ),
            SerializedTaintAssignAction(
                kind = TAINT_MARK,
                pos = PositionBaseWithModifiers.WithModifiers(Argument(0), listOf(PositionModifier.AnyField))
            )
        )
    )

    private fun starredCleaner(function: String = "clean") = SerializedRule.Cleaner(
        function = functionMatcher(TEST_CLS, function),
        cleans = listOf(
            SerializedTaintCleanAction(
                taintKind = TAINT_MARK,
                pos = PositionBaseWithModifiers.BaseOnly(Argument(0))
            ),
            SerializedTaintCleanAction(
                taintKind = TAINT_MARK,
                pos = PositionBaseWithModifiers.WithModifiers(Argument(0), listOf(PositionModifier.AnyField))
            )
        )
    )

    private fun baseOnlyCleaner() = SerializedRule.Cleaner(
        function = functionMatcher(TEST_CLS, "clean"),
        cleans = listOf(
            SerializedTaintCleanAction(
                taintKind = TAINT_MARK,
                pos = PositionBaseWithModifiers.BaseOnly(Argument(0))
            )
        )
    )

    private fun config(entryPointMethod: String) = SerializedTaintConfig(
        entryPoint = listOf(wholeObjectEntryPoint(entryPointMethod)),
        cleaner = listOf(starredCleaner()),
        sink = listOf(sinkRule(TEST_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    private fun baseOnlyCleanConfig(entryPointMethod: String) = SerializedTaintConfig(
        entryPoint = listOf(wholeObjectEntryPoint(entryPointMethod)),
        cleaner = listOf(baseOnlyCleaner()),
        sink = listOf(sinkRule(TEST_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    private fun anyFieldOnlyEntryPoint(entryPointMethod: String) = SerializedRule.EntryPoint(
        function = functionMatcher(TEST_CLS, entryPointMethod),
        taint = listOf(
            SerializedTaintAssignAction(
                kind = TAINT_MARK,
                pos = PositionBaseWithModifiers.WithModifiers(Argument(0), listOf(PositionModifier.AnyField))
            )
        )
    )

    private fun anyFieldOnlyConfig(entryPointMethod: String) = SerializedTaintConfig(
        entryPoint = listOf(anyFieldOnlyEntryPoint(entryPointMethod)),
        cleaner = listOf(starredCleaner()),
        sink = listOf(sinkRule(TEST_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
    )

    @Test
    fun `any-field-only taint - unsanitized sibling edge stays reported`() {
        // No base mark: the whole transport rides the abstract-initial summary edges, so a
        // storage that smears the sanitized sibling's exclusions onto the unsanitized edge
        // loses this finding.
        assertReachable(
            config = anyFieldOnlyConfig("uncleanedFlow"),
            testCls = TEST_CLS,
            entryPointName = "uncleanedFlow",
            ruleId = RULE_ID,
            testName = "any-field-only uncleaned sibling flow"
        )
    }

    @Test
    open fun `any-field-only taint - sanitized sibling edge stays clean`() {
        assertNotReachable(
            config = anyFieldOnlyConfig("cleanedFlow"),
            testCls = TEST_CLS,
            entryPointName = "cleanedFlow",
            testName = "any-field-only cleaned sibling flow"
        )
    }

    @Test
    fun `branch-conditional clean keeps the unsanitized path reported`() {
        // One branch cleans, the other does not: the unsanitized path must stay reported.
        // PROBE for reviewer's concern: intra-method edge storages union one exclusion slot
        // per (initial AP, statement) across lineages, smearing the sanitizer's exclusions
        // onto the unsanitized branch at the join.
        assertReachable(
            config = config("conditionalCleanFlow"),
            testCls = TEST_CLS,
            entryPointName = "conditionalCleanFlow",
            ruleId = RULE_ID,
            testName = "branch-conditional clean flow"
        )
    }

    @Test
    @Disabled // todo: fix automata
    fun `base-only clean keeps the whole-object field taint through the wrapper`() {
        // The clean removes only the base-value mark; the any-field mark survives the call
        // and the sanitized-side read stays tainted. This pins the cleaner-lineage
        // CONTINUATION: the fact enters the resolved `clean` via call-to-start and must
        // re-emerge from its identity summary.
        assertReachable(
            config = baseOnlyCleanConfig("cleanedFlow"),
            testCls = TEST_CLS,
            entryPointName = "cleanedFlow",
            ruleId = RULE_ID,
            testName = "base-only clean continuation flow"
        )
    }

    @Test
    fun `starred clean in a summarized wrapper with only the cleaned flow`() {
        assertNotReachable(
            config = config("cleanOnlyFlow"),
            testCls = TEST_CLS,
            entryPointName = "cleanOnlyFlow",
            testName = "clean-only wrapper flow"
        )
    }

    @Test
    open fun `starred clean survives an unsanitized sibling edge from the same initial fact`() {
        assertNotReachable(
            config = config("cleanedFlow"),
            testCls = TEST_CLS,
            entryPointName = "cleanedFlow",
            testName = "cleaned sibling flow"
        )
    }

    @Test
    fun `unsanitized sibling edge from the same initial fact stays reported`() {
        assertReachable(
            config = config("uncleanedFlow"),
            testCls = TEST_CLS,
            entryPointName = "uncleanedFlow",
            ruleId = RULE_ID,
            testName = "uncleaned sibling flow"
        )
    }

    // The clean and the read inside ONE summarized helper: the claim must be effective within
    // the helper's own summary computation, not only after transit to the caller's fact.

    @Test
    open fun `in-helper starred clean silences the read in the same summary`() {
        assertNotReachable(
            config = config("helperCleanReadFlow"),
            testCls = TEST_CLS,
            entryPointName = "helperCleanReadFlow",
            testName = "in-helper clean-then-read flow"
        )
    }

    @Test
    open fun `in-helper read without a clean stays reported`() {
        assertReachable(
            config = config("helperReadFlow"),
            testCls = TEST_CLS,
            entryPointName = "helperReadFlow",
            ruleId = RULE_ID,
            testName = "in-helper read control"
        )
    }

    @Test
    open fun `in-helper nested starred clean silences the read`() {
        assertNotReachable(
            config = config("helperNestedCleanReadFlow"),
            testCls = TEST_CLS,
            entryPointName = "helperNestedCleanReadFlow",
            testName = "in-helper nested clean-then-read flow"
        )
    }

    @Test
    open fun `clean plus depth-2 constant store returns a silent object`() {
        val nodeConfig = SerializedTaintConfig(
            entryPoint = listOf(wholeObjectEntryPoint("nodeCleanAssignFlow")),
            cleaner = listOf(starredCleaner("cleanNode")),
            sink = listOf(sinkRule(TEST_CLS, "sink", RULE_ID, listOf(Argument(0) to TAINT_MARK)))
        )
        assertNotReachable(
            config = nodeConfig,
            testCls = TEST_CLS,
            entryPointName = "nodeCleanAssignFlow",
            testName = "clean-then-assign leaf flow"
        )
    }
}

/**
 * The sibling cases pass precisely: `wrap` stores its argument into `p.raw` before the starred
 * clean and into `p.val` after it, and the clean's residual claim rides the exit tree's `.val`
 * abstraction (AbstractionExclusions) without ever meeting `.raw`. The unsanitized sibling stays
 * reported, the sanitized one stays silent.
 */
class TreeDeepCleanSummaryAnalysisTest : DeepCleanSummaryAnalysisTest()

class AutomataDeepCleanSummaryAnalysisTest : DeepCleanSummaryAnalysisTest() {
    override val apMode: ApMode = ApMode.Automata

    // The in-helper control is red in this mode for the documented reason (taint dropped across
    // the intervening call), so the two silent cases it guards would pass vacuously — all three
    // stay disabled together until the Automata intervening-call fix.
    @Test
    @Disabled // todo: fix automata -- taint dropped across the intervening call
    override fun `in-helper read without a clean stays reported`() =
        super.`in-helper read without a clean stays reported`()

    @Test
    @Disabled // todo: fix automata -- control above is red, a pass here is vacuous
    override fun `in-helper starred clean silences the read in the same summary`() =
        super.`in-helper starred clean silences the read in the same summary`()

    @Test
    @Disabled // todo: fix automata -- control above is red, a pass here is vacuous
    override fun `in-helper nested starred clean silences the read`() =
        super.`in-helper nested starred clean silences the read`()
}
