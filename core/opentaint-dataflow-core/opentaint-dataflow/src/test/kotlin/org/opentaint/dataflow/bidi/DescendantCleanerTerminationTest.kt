package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.driver.IncreasingLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Historical pre-R35/R36 diagnostic on unchanged production. The earlier
 * same-head MUST policy did not cover cleaning x.f from x.MUST.
 * The only call action is a configured cleaner: no unresolved transfer,
 * pass rule, loop, recursion, write or user-provided summary is involved. */
class DescendantCleanerTerminationTest {
    private enum class Source { UNIFORM, ROOT, CLEANED_POINT, SIBLING }
    private data class Case(val main: MethodKey, val x: AccessPathBase, val field: Int)
    private fun program(f: DriverFixtures, source: Source, reach: CleanReach = CleanReach.EXACT, depth: Int = 1, allMarks: Boolean = false): Case {
        val p = f.program
        val main = p.method("descendant cleaner", listOf(listOf(1), listOf(2), emptyList()), 2).key()
        val emptyCleaner = p.method("fully analyzed empty cleaner body", listOf(listOf(1), emptyList()), 1).key()
        val arg = AccessPathBase.Argument(0)
        val x = AccessPathBase.LocalVar(0)
        val field = p.field("f"); val sibling = p.field("g")
        val cleaned = List(depth) { if (it % 2 == 0) field else sibling }
        val t = p.mark("T"); val mark = MarkSlot.Concrete(t)
        val path = when (source) {
            Source.UNIFORM, Source.ROOT -> emptyList()
            Source.CLEANED_POINT -> cleaned
            Source.SIBLING -> listOf(sibling)
        }
        val seed = PathEdge(ZERO_FACT, PathFact(x, path,
            if (source == Source.UNIFORM) Tail.ANY_TAINT else Tail.EXACT, mark), ExclusionSet.Empty)
        p.entry(main, RuleStatement(f.summary(ZERO_KEEP, seed), StatementSummary.EMPTY, emptyList()))
        p.call(main, 1, CallPlan(setOf(x), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(x, emptyList(), arg, emptyList()))),
            CallStage.Actions(BOUND, ADDED, listOf(CleanStep.Clean(Cleaner(arg, f.manager.path(cleaned), reach, if (allMarks) null else t)))),
            CallStage.Callees(ADDED, RETURNED, listOf(emptyCleaner)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(arg, emptyList(), x, emptyList())))
        ), emptyList(), BEFORE, AFTER))
        val observation = SinkRule(f.rule("observe remaining T"), 0,
            listOf(p.pattern(x, tail = Tail.ANY, mark = mark)), emptyList())
        p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(observation)),
            false, emptySet()))
        return Case(main, x, field)
    }
    private fun diagnostic(reach: CleanReach = CleanReach.EXACT, depth: Int = 1, allMarks: Boolean = false) {
        DriverFixtures().use { f ->
            val c = program(f, Source.UNIFORM, reach, depth, allMarks)
            val report = f.driver(TerminationBaselinePolicy, 30.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(c.main))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertTrue(f.processed.filter { it.method == c.main }.all { it.delta.premise.isZero })
            for (result in f.results) {
                val actor = result.analyzers.single { it.key == c.main }
                assertTrue(actor.summaries.all().none { (_, facts) -> facts.base != AccessPathBase.Zero })
                assertTrue(actor.outgoingTargets.any { it.premise.isZero && it.target == Target.DemandTarget })
                assertTrue(actor.targets.none { it.target is Target.NormalTarget })
                println("DESCENDANT_CLEANER reach=$reach depth=$depth all=$allMarks run=${result.runIndex} outgoing=${actor.outgoingTargets.size} normal=${actor.targets.count{it.target is Target.NormalTarget}}")
            }
            assertTrue(f.processed.filter { it.method == c.main }.all { row -> f.ops.leaves(row.delta.facts).all { it.fact.path.isEmpty() } })
        }
    }
    @Test fun `descendant exact cleaner repeats Target demand through diagnostic run101`() = diagnostic()
    @Test fun `nested whole subtree cleaner repeats through diagnostic run101`() = diagnostic(CleanReach.AT_AND_BELOW, 2)
    @Test fun `nested below cleaner repeats through diagnostic run101`() = diagnostic(CleanReach.BELOW, 2)
    @Test fun `nested RemoveAll repeats through diagnostic run101`() = diagnostic(CleanReach.AT_AND_BELOW, 2, true)
    private fun control(source: Source, reach: CleanReach, expected: Int, latest: Int) {
        DriverFixtures().use { f ->
            val c = program(f, source, reach)
            val report = f.driver(IncreasingLimits, 20.seconds, run1MarkMode = MarkMode.FULL).analyze(listOf(c.main))
            println("DESCENDANT_CONTROL source=$source reach=$reach latest=${report.end.run} end=${report.end.reason} normal=${report.entries.count{!it.provisional}}")
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(latest, report.end.run)
            assertEquals(expected, report.entries.count { !it.provisional })
        }
    }
    @Test fun `the object root is a real uncleaned witness`() = control(Source.ROOT, CleanReach.EXACT, 1, 1)
    @Test fun `the selected point itself is removed`() = control(Source.CLEANED_POINT, CleanReach.EXACT, 0, 1)
    @Test fun `a sibling point is preserved`() = control(Source.SIBLING, CleanReach.EXACT, 1, 1)
    @Test fun `whole subtree cleanup has an existing exclusion answer`() = control(Source.UNIFORM, CleanReach.AT_AND_BELOW, 1, 3)
}
