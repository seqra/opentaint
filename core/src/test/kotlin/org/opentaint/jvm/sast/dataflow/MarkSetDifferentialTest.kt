package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.common.sast.dataflow.assertSameMarkSetFindings
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

/**
 * Spec §8 Layer 3, the new samples: each program runs under the baseline and under the mark-set
 * selection, and the two finding sets must be equal (spec §2). Each sample pins one design bug
 * (D1, D4) or one model-engine gap (G1, G4, G5, G6) of spec §5.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class MarkSetDifferentialTest : AnalysisTest() {
    private companion object {
        const val TEST_CLS = "test.samples.MarkSetDiffSamples"

        const val MARK_A = "a"
        const val MARK_B = "b"
        const val MARK_C = "c"
        const val MARK_CHECKED = "checked"
        const val MARK_THROWN = "thrown"
        const val MARK_TRANSFORMED = "transformed"
        const val MARK_UNRELATED = "unrelated"

        const val RULE_BOTH = "d1-both"
        const val RULE_JOINED = "g3-joined"
        const val RULE_CHECK = "g1-check"
        const val RULE_CHECKED = "g1-checked"
        const val RULE_SINK = "g4-sink"
        const val RULE_EXIT_PASS_BACK = "g5-exit-pass-back"
        const val RULE_EXIT_PRODUCE = "g5-exit-produce"
        const val RULE_THROWN = "g6-thrown"
        const val RULE_TRANSFORMED = "d4-transformed"
        const val RULE_UNRELATED = "d4-unrelated"
    }

    override val sourceFileExtension: String = "java"

    /**
     * Runs [entryPoints] in the baseline and in the mark-set mode given by [markSetOptions], whatever
     * the differential switch, and asserts equal findings.
     */
    private fun differential(
        config: SerializedTaintConfig,
        vararg entryPoints: String,
        markSetOptions: MarkSetScanOptions = MarkSetScanOptions(enabled = true),
    ): Differential {
        val eps = entryPoints.toList()
        val baseline = runAnalysisOnce(config, TEST_CLS, eps, MarkSetScanOptions())
        val markSet = runAnalysisOnce(config, TEST_CLS, eps, markSetOptions)
        val outcome = assertIs<MarkSetOutcome.Selected>(markSet.markSetOutcome, "the mark-set phase did not select")
        assertSameMarkSetFindings(baseline.gated, markSet.gated, "$TEST_CLS$eps")
        return Differential(baseline, markSet, outcome)
    }

    private class Differential(val baseline: AnalysisRun, val markSet: AnalysisRun, val outcome: MarkSetOutcome.Selected)

    /** The baseline's confirmed findings of [ruleId], as the names of their sink statements' methods. */
    private fun Differential.baselineFiredIn(ruleId: String): List<String> =
        baseline.confirmed.filter { it.ruleId == ruleId }.map { (it.statement as JIRInst).location.method.name }

    private fun mark(name: String, base: PositionBase) =
        SerializedCondition.ContainsMark(name, PositionBaseWithModifiers.BaseOnly(base))

    private fun assign(name: String, base: PositionBase) =
        SerializedTaintAssignAction(kind = name, pos = PositionBaseWithModifiers.BaseOnly(base))

    private fun sink(method: String, id: String, condition: SerializedCondition, endMarks: List<SerializedTaintAssignAction>? = null) =
        SerializedRule.Sink(function = functionMatcher(TEST_CLS, method), condition = condition, trackFactsReachAnalysisEnd = endMarks, id = id)

    private fun source(method: String, mark: String, condition: SerializedCondition? = null) =
        SerializedRule.Source(
            function = functionMatcher(TEST_CLS, method),
            condition = condition,
            taint = listOf(assign(mark, PositionBase.Result)),
        )

    @Test
    fun `D1 - a conjunctive sink in a shared callee fires on facts from two entry points`() {
        val config = SerializedTaintConfig(
            source = listOf(source("sourceA", MARK_A), source("sourceB", MARK_B)),
            sink = listOf(
                sink(
                    "sinkBoth", RULE_BOTH,
                    SerializedCondition.and(listOf(mark(MARK_A, Argument(0)), mark(MARK_B, Argument(1)))),
                )
            ),
        )

        val run = differential(config, "d1EntryOne", "d1EntryTwo")
        assertEquals(listOf("d1Shared"), run.baselineFiredIn(RULE_BOTH), "the baseline sink did not fire")
        assertTrue(run.markSet.confirmed.any { it.ruleId == RULE_BOTH }, "the mark-set sink did not fire")
    }

    @Test
    fun `G3 - a joined source in a shared callee with three roots, exact and under 4*`() {
        val config = SerializedTaintConfig(
            source = listOf(
                source("sourceA", MARK_A),
                source("sourceB", MARK_B),
                source(
                    "join", MARK_C,
                    condition = SerializedCondition.and(listOf(mark(MARK_A, Argument(0)), mark(MARK_B, Argument(1)))),
                ),
            ),
            sink = listOf(sink("sink", RULE_JOINED, mark(MARK_C, Argument(0)))),
        )

        val entryPoints = arrayOf("g3EntryOne", "g3EntryTwo", "g3EntryThree", "g3EntryBoth")
        val exact = differential(config, *entryPoints)
        // The premise, as the engine realizes it: the join in the shared callee is over two
        // caller-supplied (fact-to-fact) facts, so its C is a non-distributive summary edge that
        // needs both A@arg0 and B@arg1 at one call site. It reaches only the control root that
        // passes both, not the third root (the model's zero-context placement over-approximates).
        assertEquals(listOf("g3EntryBoth"), exact.baselineFiredIn(RULE_JOINED), "the joined C reaches an unexpected root")

        differential(config, *entryPoints, markSetOptions = MarkSetScanOptions(enabled = true, relaxed = true))
    }

    @Test
    fun `G1 - a sink end fact is used across roots`() {
        val config = SerializedTaintConfig(
            source = listOf(source("sourceA", MARK_A)),
            cleaner = listOf(
                SerializedRule.Cleaner(
                    function = functionMatcher(TEST_CLS, "uncheck"),
                    cleans = listOf(
                        SerializedTaintCleanAction(
                            taintKind = MARK_CHECKED, pos = PositionBaseWithModifiers.BaseOnly(Argument(0))
                        )
                    ),
                )
            ),
            sink = listOf(
                sink("check", RULE_CHECK, mark(MARK_A, Argument(0)), listOf(assign(MARK_CHECKED, Argument(0)))),
                sink("sinkChecked", RULE_CHECKED, mark(MARK_CHECKED, Argument(0))),
            ),
        )

        val run = differential(config, "g1EntryOne", "g1EntryTwo", "g1EntryCleaned")
        // The premise: the second root never sees mark A, yet its sink fires on the end mark of
        // the check in the shared callee (a zero-context fact).
        assertTrue("g1EntryTwo" in run.baselineFiredIn(RULE_CHECKED), "the end mark does not reach the second root")
    }

    @Test
    fun `G4 - a cleaner conditioned on a mark still cleans the needed mark of the same tree`() {
        val anyField = PositionBaseWithModifiers.WithModifiers(Argument(0), listOf(PositionModifier.AnyField))
        val config = SerializedTaintConfig(
            source = listOf(
                source("sourceA", MARK_A),
                SerializedRule.Source(function = functionMatcher(TEST_CLS, "addBPair"), taint = listOf(assign(MARK_B, Argument(0)))),
            ),
            cleaner = listOf(
                SerializedRule.Cleaner(
                    function = functionMatcher(TEST_CLS, "cleanIfB"),
                    condition = mark(MARK_B, Argument(0)),
                    cleans = listOf(
                        SerializedTaintCleanAction(taintKind = MARK_A, pos = PositionBaseWithModifiers.BaseOnly(Argument(0))),
                        SerializedTaintCleanAction(taintKind = MARK_A, pos = anyField),
                    ),
                )
            ),
            sink = listOf(sink("sink", RULE_SINK, mark(MARK_A, Argument(0)))),
        )

        val run = differential(config, "g4EntryFieldCleaned", "g4EntryKept")
        // The premise: the cleaner fires on the tree holding both marks. Mark B is needed only
        // through the cleaner's atom.
        assertEquals(listOf("g4EntryKept"), run.baselineFiredIn(RULE_SINK), "the cleaner does not clean in the baseline")
    }

    @Test
    fun `G5 - an exit sink on a fact-to-fact edge`() {
        val config = SerializedTaintConfig(
            source = listOf(source("sourceA", MARK_A)),
            methodExitSink = listOf(
                methodExitSinkRule(TEST_CLS, "g5PassBack", RULE_EXIT_PASS_BACK, MARK_A),
                methodExitSinkRule(TEST_CLS, "g5Produce", RULE_EXIT_PRODUCE, MARK_A),
            ),
        )

        val run = differential(config, "g5Entry")
        assertEquals(run.baseline.confirmed.size, run.markSet.confirmed.size, "the finding counts differ")
        // The premise: the exit sink fires on the zero-to-fact edge only.
        assertEquals(emptyList(), run.baselineFiredIn(RULE_EXIT_PASS_BACK), "the exit sink fires on a fact-to-fact edge")
        assertEquals(listOf("g5Produce"), run.baselineFiredIn(RULE_EXIT_PRODUCE), "the exit sink does not fire")
    }

    @Test
    fun `G6 - an exit source at a throw`() {
        val config = SerializedTaintConfig(
            source = listOf(source("sourceException", MARK_A)),
            methodExitSource = listOf(
                SerializedRule.MethodExitSource(
                    function = functionMatcher(TEST_CLS, "g6Throw"),
                    condition = mark(MARK_A, PositionBase.Result),
                    taint = listOf(assign(MARK_THROWN, PositionBase.Result)),
                )
            ),
            methodExitSink = listOf(methodExitSinkRule(TEST_CLS, "g6Throw", RULE_THROWN, MARK_THROWN)),
        )

        val run = differential(config, "g6Entry")
        // The premise: the exit source fires at the throw (its only exit), where the exit sink sees it.
        assertEquals(listOf("g6Throw"), run.baselineFiredIn(RULE_THROWN), "the exit source does not fire at the throw")
    }

    @Test
    fun `D4 - an unrelated rule's source actions are deselected`() {
        val config = SerializedTaintConfig(
            source = listOf(
                source("sourceA", MARK_A),
                source("transform", MARK_TRANSFORMED, condition = mark(MARK_A, Argument(0))),
                source("sourceUnrelated", MARK_UNRELATED),
            ),
            sink = listOf(
                sink("sinkTransformed", RULE_TRANSFORMED, mark(MARK_TRANSFORMED, Argument(0))),
                sink("sinkUnrelated", RULE_UNRELATED, mark(MARK_UNRELATED, Argument(0))),
            ),
        )

        val run = differential(config, "d4Entry")
        val outcome = run.outcome

        fun JIRInst.callee() = callExpr?.method?.name
        val unrelatedCalls = outcome.covered.filter { (it as JIRInst).callee() == "sourceUnrelated" }
        assertTrue(unrelatedCalls.isNotEmpty(), "the sourceUnrelated call is not a covered statement")

        val selectedSources = outcome.rules.entries.flatMap { (statement, rules) ->
            rules.entries.filter { it.key is TaintMethodSource }.map { (statement as JIRInst).callee() to it.value }
        }
        assertTrue(
            selectedSources.none { it.first == "sourceUnrelated" },
            "the unrelated source is selected: $selectedSources"
        )
        assertTrue(selectedSources.any { it.first == "sourceA" }, "the chain's source is not selected: $selectedSources")
        assertTrue(selectedSources.any { it.first == "transform" }, "the transformer is not selected: $selectedSources")
    }
}
