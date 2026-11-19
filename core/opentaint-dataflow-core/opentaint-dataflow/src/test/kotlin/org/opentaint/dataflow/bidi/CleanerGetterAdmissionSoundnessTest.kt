package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Diagnostic for the retained cleaner/admission contract. No proposed tail
 * or completion implementation is installed by this test. */
class CleanerGetterAdmissionSoundnessTest {
    private fun run(clean: Boolean, deep: Boolean): Pair<Int, Int> =
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("cleaner getter root", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val helper = p.method("cleaner getter helper", listOf(listOf(1), listOf(2), listOf(3), emptyList()), 3).key()
            val a = AccessPathBase.LocalVar(0)
            val r = AccessPathBase.LocalVar(1)
            val arg = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val g = p.field("g"); val h = p.field("h")
            val t = MarkSlot.Concrete(p.mark("T"))
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT, PathFact(a, if (deep) listOf(g, h) else listOf(g), Tail.ANY_TAINT, t), ExclusionSet.Empty)),
                StatementSummary.EMPTY, emptyList()))
            val identity = f.summary(ZERO_KEEP, keepEdge(arg))
            p.call(helper, 1, CallPlan(setOf(arg), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
                CallStage.Actions(BOUND, ADDED, if (clean)
                    listOf(CleanStep.Clean(Cleaner(arg, null, CleanReach.EXACT, t.mark))) else emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, identity),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
            ), emptyList(), BEFORE, AFTER))
            p.statement(helper, 2, MicroEdgeBuilder().apply { read(ret, arg, listOf(g)) }.build())
            p.call(main, 1, CallPlan(setOf(a, r), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN,
                    f.summary(ZERO_KEEP, starEdge(a, emptyList(), arg, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(helper)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(ret, emptyList(), r, emptyList()), starEdge(arg, emptyList(), a, emptyList()))),
            ), emptyList(), BEFORE, AFTER))
            val observation = SinkRule(f.rule("getter observation"), 0,
                listOf(p.pattern(r, tail = Tail.ANY, mark = t)), emptyList())
            p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(observation)), false, emptySet()))
            val report = f.driver(FixedLimits(List(15) { maxOf(1, it) }), 20.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            report.end.run to report.entries.count { !it.provisional }
        }

    @Test fun `root cleanup plus deeper precise input exposes the retained admission gap`() {
        // The expected result documents the unfixed gap, not correct concrete behavior.
        assertEquals(3 to 0, run(clean = true, deep = true))
    }

    @Test fun `without cleanup the NORMAL FLOW route keeps the observation`() {
        val (latest, normal) = run(clean = false, deep = true)
        assertTrue(latest <= 5)
        assertEquals(1, normal)
    }

    @Test fun `a same-head precise input still admits after cleanup`() {
        val (latest, normal) = run(clean = true, deep = false)
        assertTrue(latest <= 5)
        assertEquals(1, normal)
    }
}
