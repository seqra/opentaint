package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Rejected non-termination candidate: backward C5 rebases the MAY requirement
 * at the forward premise's first field. No cleaner or pass rule is involved. */
class ConditionalMarkMayCycleTest {
    private data class Case(val main: MethodKey, val make: MethodKey, val field: Int)

    private fun program(f: DriverFixtures, conditionAtField: Boolean = false,
                        sourceTail: Tail = Tail.ANY_TAINT): Case {
        val p = f.program
        val main = p.method("conditional main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
        val make = p.method("conditional make", listOf(listOf(1), listOf(2), listOf(3), emptyList()), 3).key()
        val x = AccessPathBase.LocalVar(0)
        val y = AccessPathBase.LocalVar(1)
        val r = AccessPathBase.LocalVar(2)
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val field = p.field("f")
        val t = MarkSlot.Concrete(p.mark("T"))
        val u = MarkSlot.Concrete(p.mark("U"))
        val source = PathEdge(ZERO_FACT, PathFact(x, listOf(field), sourceTail, t), ExclusionSet.Empty)
        p.entry(main, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))

        // make(p) { r=new Box(); produceUIfAnyT(p,r); return r; }
        // Ordinary source rule: CM(p.MAY,T) => assign U at r.EXACT.
        val builder = RulePredicate.Builder(f.cancellation)
        val condition = p.pattern(arg, if (conditionAtField) listOf(field) else emptyList(), Tail.ANY, t)
        val predicate = builder.build(builder.leaf(condition))
        val id = RuleOccurrenceId(FormKey(FormOwner(), make.method, make, p.inst(make, 1)), RuleKind.CALL_SOURCE, 0)
        val action = SourceAction(ActionId(id, ActionRole.SOURCE, 0), p.pattern(r, mark = u).fact)
        p.statement(make, 1, StatementSummary(emptySet(), emptyList(), emptyList(), emptyMap(),
            sources = listOf(SourceRuleOccurrence(id, predicate, listOf(action)))))
        p.statement(make, 2, f.summary(ZERO_KEEP, starEdge(r, emptyList(), ret, emptyList())))

        p.call(main, 1, CallPlan(setOf(x,y), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN,
                f.summary(ZERO_KEEP, starEdge(x, emptyList(), arg, emptyList()))),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Callees(ADDED, RETURNED, listOf(make)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK,
                f.summary(ZERO_KEEP, starEdge(ret, emptyList(), y, emptyList()),
                    starEdge(arg, emptyList(), x, emptyList())))
        ), emptyList(), BEFORE, AFTER))
        val observation = SinkRule(f.rule("observe U"), 0, listOf(p.pattern(y, mark = u)), emptyList())
        p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(observation)), false, emptySet()))
        return Case(main, make, field)
    }

    @Test fun `backward paired C5 advances the conditional producer to its field`() {
        DriverFixtures().use { f ->
            val c = program(f)
            val report = f.driver(TerminationBaselinePolicy, 30.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(c.main))
            for (run in f.results) {
                val make = run.analyzers.singleOrNull { it.key == c.make }
                val main = run.analyzers.single { it.key == c.main }
                println("CONDITIONAL_MAY run=${run.runIndex} targets=${main.outgoingTargets.size}")
                make?.summaries?.all()?.forEach { (initial, facts) ->
                    println("REL ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(5, report.end.run)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertTrue(f.results.filter { it.runIndex < 5 }.all { run -> run.analyzers.single { it.key == c.main }.outgoingTargets
                .any { it.premise.isZero && it.target == Target.DemandTarget } })
            assertEquals(1, report.entries.size)
        }
    }

    @Test fun `a field-qualified condition reaches the same-head MUST query`() {
        DriverFixtures().use { f ->
            val c = program(f, conditionAtField = true)
            val report = f.driver(FixedLimits(List(11) { maxOf(1,it) }), 30.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(c.main))
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(3, report.end.run)
            assertEquals(1, report.entries.size)
        }
    }

    @Test fun `an exact first-field producer avoids the STAR demand start`() {
        DriverFixtures().use { f ->
            val c = program(f, sourceTail = Tail.EXACT)
            val report = f.driver(FixedLimits(List(11) { maxOf(1,it) }), 30.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(c.main))
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(3, report.end.run)
            assertEquals(1, report.entries.size)
        }
    }

}
