package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Historical production behavior before the selected MUST-preserving
 * cleaner revision. Production is not changed by the specification update.
 * The ceiling is a test budget, not the proof of non-termination. */
class UniformRootCleanerTerminationTest {
    private fun program(f: DriverFixtures, reach: CleanReach? = CleanReach.EXACT,
                        sinkTail: Tail = Tail.ANY, preciseChildSource: Boolean = false): MethodKey {
        val p = f.program
        // main: x = sourceTreeT(); removeTAtRoot(x); sinkTreeT(x).
        val main = p.method("uniform root cleaner", listOf(listOf(1), listOf(2), emptyList()), 2).key()
        val x = AccessPathBase.LocalVar(0)
        val t = p.mark("T")
        val mark = MarkSlot.Concrete(t)
        val source = PathEdge(ZERO_FACT, PathFact(x,
            if (preciseChildSource) listOf(p.field("f")) else emptyList(),
            if (preciseChildSource) Tail.EXACT else Tail.ANY_TAINT, mark), ExclusionSet.Empty)
        p.entry(main, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
        val identity = f.summary(ZERO_KEEP, keepEdge(x))
        p.call(main, 1, CallPlan(setOf(x), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
            CallStage.Actions(BOUND, ADDED, reach?.let {
                listOf(CleanStep.Clean(Cleaner(x, null, it, t)))
            }.orEmpty()),
            CallStage.Edges(ADDED, RETURNED, UNRESOLVED, identity),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
        ), emptyList(), BEFORE, AFTER))
        val sink = SinkRule(f.rule("root-cleaner tree sink"), 0,
            listOf(p.pattern(x, tail = sinkTail, mark = mark)), emptyList())
        p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)),
            false, emptySet()))
        return main
    }

    @Test fun `uniform source exact-root selected cleanup renews the same target through run101`() {
        DriverFixtures().use { f ->
            val main = program(f)
            val driver = f.driver(TerminationBaselinePolicy, 20.seconds,
                run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(main))
            for (result in f.results) {
                val actor = result.analyzers.single { it.key == main }
                val data = actor.summaries.all().count { (_, value) -> value.base != AccessPathBase.Zero }
                println("ROOT_CLEANER_CYCLE run=${result.runIndex} demandTargets=${actor.outgoingTargets.size} " +
                    "normalTargets=${actor.targets.count { it.target is Target.NormalTarget }} dataSummaries=$data")
                assertEquals(0, data, "No local x fact becomes a method DATA summary")
            }
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertEquals((1..TERMINATION_BASELINE_LAST_RUN).toList(), f.results.map { it.runIndex })
            assertTrue(f.processed.all { it.delta.premise.isZero },
                "No method DATA initial, MUST or MAY premise is introduced")
            assertTrue(f.processed.all { row -> f.ops.leaves(row.delta.facts).all { it.fact.path.isEmpty() } },
                "All processed field chains have length zero; no truncation can cause this cycle")
            for (result in f.results) {
                val actor = result.analyzers.single { it.key == main }
                assertEquals(1, actor.outgoingTargets.size)
                assertTrue(actor.outgoingTargets.any { it.premise.isZero && it.target == Target.DemandTarget },
                    "run-${result.runIndex} must recompute the same ZERO -> DemandTarget")
                assertTrue(actor.targets.none { it.target is Target.NormalTarget })
            }
        }
    }

    @Test fun `without cleaner the uniform finding is normal in run1`() {
        DriverFixtures().use { f ->
            val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL)
                .analyze(listOf(program(f, reach = null)))
            assertEquals(1, report.end.run)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(1, report.entries.size)
        }
    }

    @Test fun `whole-position cleaner kills the candidate in run1`() {
        DriverFixtures().use { f ->
            val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL)
                .analyze(listOf(program(f, reach = CleanReach.AT_AND_BELOW)))
            assertEquals(1, report.end.run)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertTrue(report.entries.isEmpty())
        }
    }

    @Test fun `exact-root sink cannot renew permission through the root cleaner`() {
        DriverFixtures().use { f ->
            val report = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), run1MarkMode = MarkMode.FULL)
                .analyze(listOf(program(f, sinkTail = Tail.EXACT)))
            assertEquals(3, report.end.run)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertTrue(report.entries.isEmpty())
        }
    }

    @Test fun `precise child source survives normally without a repetition`() {
        DriverFixtures().use { f ->
            val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL)
                .analyze(listOf(program(f, preciseChildSource = true)))
            assertEquals(1, report.end.run)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(1, report.entries.size)
        }
    }
}
