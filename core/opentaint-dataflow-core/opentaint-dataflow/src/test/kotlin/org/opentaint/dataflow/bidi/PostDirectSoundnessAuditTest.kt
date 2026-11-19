package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.driver.IncreasingLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Cold controls for precise observations and concrete unary rule actions.
 * No proposal adapter or production matching change is installed. */
class PostDirectSoundnessAuditTest {
    private fun conditional(depth: Int, uniform: Boolean, sameMark: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("point audit main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val make = p.method("point audit conditional", listOf(listOf(1), listOf(2), listOf(3), emptyList()), 3).key()
            val x = AccessPathBase.LocalVar(0)
            val y = AccessPathBase.LocalVar(1)
            val temporary = AccessPathBase.LocalVar(2)
            val arg = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val field = p.field("f"); val other = p.field("g")
            val path = List(depth) { if (it % 2 == 0) field else other }
            val t = MarkSlot.Concrete(p.mark("T"))
            val u = if (sameMark) t else MarkSlot.Concrete(p.mark("U"))
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT, PathFact(x, path, if (uniform) Tail.ANY_TAINT else Tail.EXACT, t), ExclusionSet.Empty)),
                StatementSummary.EMPTY, emptyList()))
            val builder = RulePredicate.Builder(f.cancellation)
            val predicate = builder.build(builder.leaf(p.pattern(arg, tail = Tail.ANY, mark = t)))
            val id = RuleOccurrenceId(FormKey(FormOwner(), make.method, make, p.inst(make, 1)), RuleKind.CALL_SOURCE, 0)
            val action = SourceAction(ActionId(id, ActionRole.SOURCE, 0), p.pattern(temporary, mark = u).fact)
            // Rule: CM(arg.MAY,T) assigns U at temporary.$.
            p.statement(make, 1, StatementSummary(setOf(arg, temporary), emptyList(), emptyList(), emptyMap(),
                sources = listOf(SourceRuleOccurrence(id, predicate, listOf(action)))))
            p.statement(make, 2, f.summary(ZERO_KEEP, starEdge(temporary, emptyList(), ret, emptyList())))
            p.call(main, 1, CallPlan(setOf(x,y), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(x, emptyList(), arg, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(make)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(ret, emptyList(), y, emptyList()), starEdge(arg, emptyList(), x, emptyList())))
            ), emptyList(), BEFORE, AFTER))
            p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(SinkRule(f.rule("observe assigned point"), 0, listOf(p.pattern(y, mark = u)), emptyList()))),
                false, emptySet()))
            val report = f.driver(IncreasingLimits, 30.seconds, run1MarkMode = MarkMode.FULL).analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(1, report.entries.count { !it.provisional })
            assertEquals(0, report.entries.count { it.provisional })
        }
    }
    @Test fun `empty method DATA demand does not stop a cut NORMAL pack application`() {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("pack audit main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val pack = p.method("pack audit helper", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val x = AccessPathBase.LocalVar(0); val y = AccessPathBase.LocalVar(1)
            val arg = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
            val field = p.field("f"); val t = MarkSlot.Concrete(p.mark("T"))
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP, PathEdge(ZERO_FACT,
                PathFact(x, listOf(field), Tail.EXACT, t), ExclusionSet.Empty)), StatementSummary.EMPTY, emptyList()))
            // Node pack(Node arg) { Node ret=new Node(); ret.f=arg; return ret; }
            p.statement(pack, 1, MicroEdgeBuilder().apply { move(ret, arg, listOf(field)) }.build())
            p.call(main, 1, CallPlan(setOf(x,y), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(x, emptyList(), arg, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(pack)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(ret, emptyList(), y, emptyList()), starEdge(arg, emptyList(), x, emptyList())))
            ), emptyList(), BEFORE, AFTER))
            p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(SinkRule(f.rule("observe packed point"), 0, listOf(p.pattern(y, tail = Tail.ANY, mark = t)), emptyList()))),
                false, emptySet()))
            val report = f.driver(IncreasingLimits, 30.seconds, run1MarkMode = MarkMode.FULL).analyze(listOf(main))
            val first = f.results.first().analyzers.single { it.key == pack }
            assertTrue(first.summaries.all().all { (_, value) -> value.layer == Layer.NORMAL })
            assertTrue(f.results.first().analyzers.single { it.key == main }.outgoingTargets.any {
                it.target == org.opentaint.dataflow.bidi.engine.Target.DemandTarget
            })
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(3, report.end.run)
            assertEquals(1, report.entries.count { !it.provisional })
        }
    }
    @Test fun `exact mark at one field satisfies the broad condition`() = conditional(1, false)
    @Test fun `exact mark at two fields satisfies the broad condition`() = conditional(2, false)
    @Test fun `exact mark at three fields satisfies the broad condition`() = conditional(3, false)
    @Test fun `uniform mark at one field satisfies the broad condition`() = conditional(1, true)
    @Test fun `uniform mark at two fields satisfies the broad condition`() = conditional(2, true)
    @Test fun `uniform mark at three fields satisfies the broad condition`() = conditional(3, true)
    @Test fun `same mark assignment retains the exact input route`() = conditional(2, false, true)
    @Test fun `same mark assignment retains the uniform input route`() = conditional(2, true, true)
}
