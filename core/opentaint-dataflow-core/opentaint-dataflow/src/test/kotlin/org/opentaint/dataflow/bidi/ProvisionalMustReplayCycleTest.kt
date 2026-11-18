package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.Record
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Synthetic conditional producer and two uniform inputs. Production is unchanged.
 * Run-101 is a diagnostic capture; the uncapped Lean recurrence is the proof. */
class ProvisionalMustReplayCycleTest {
    private class Output : LocalRelationOut {
        val facts = arrayListOf<Facts>()
        override fun data(original: PremiseKey, value: Facts) { facts += value }
        override fun target(original: PremiseKey, target: Target) = error("Unexpected Target")
        override fun markRequest(mark: TaintMark) = error("Unexpected mark request")
    }

    @Test fun `a whole MUST record has a provisional result on the field input`() {
        val f = StoreFixtures()
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val field = f.field("f")
        val t = MarkSlot.Concrete(f.mark("T"))
        val u = MarkSlot.Concrete(f.mark("U"))
        val actual = f.fact(arg, listOf(field), Tail.ANY_TAINT, t)
        val conclusion = f.fact(ret, mark = u)
        val whole = f.manager.initial(f.pattern(arg, tail = Tail.ANY_TAINT, mark = t))
        val child = f.manager.initial(f.pattern(arg, listOf(field), Tail.ANY_TAINT, t))
        val app = LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 4))
        val broadOutput = Output()
        assertTrue(app.applyRecord(actual, f.manager.zero,
            Record(f.method, Direction.FORWARD, whole, conclusion), broadOutput))
        assertEquals(Layer.DEMAND, broadOutput.facts.single().layer)
        assertEquals(listOf(f.pattern(ret, mark = u)), f.ops.leaves(broadOutput.facts.single()).toList())
        val narrowOutput = Output()
        assertTrue(app.applyRecord(actual, f.manager.zero,
            Record(f.method, Direction.FORWARD, child, conclusion), narrowOutput))
        assertEquals(Layer.NORMAL, narrowOutput.facts.single().layer)
        val current = Output()
        assertFalse(app.applyCurrent(actual, f.manager.zero, whole, conclusion, current))
        assertTrue(current.facts.isEmpty(), "Only saved replay adds the provisional result")
        val packet = ConclusionGroup(f.manager, f.manager.newInterners())
        (broadOutput.facts + narrowOutput.facts).forEach { packet.addAll(it) }
        assertEquals(setOf(Layer.NORMAL, Layer.DEMAND), packet.all().map { it.layer }.toSet(),
            "Complete packet canonicalization keeps the two support layers")
    }

    @Test fun `reversing the whole record renews MAY rather than an exact point`() {
        val f = StoreFixtures()
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val t = MarkSlot.Concrete(f.mark("T"))
        val u = MarkSlot.Concrete(f.mark("U"))
        val whole = f.manager.initial(f.pattern(arg, tail = Tail.ANY_TAINT, mark = t))
        val record = Record(f.method, Direction.FORWARD, whole, f.fact(ret, mark = u))
        val view = record.reversedAt(f.pattern(ret, mark = u)).single()
        assertEquals(f.pattern(ret, mark = u), view.premise)
        assertEquals(f.pattern(arg, tail = Tail.ANY, mark = t).fact, view.result.fact)
        assertTrue(view.result.demand)
    }

    @Test fun `direct saved MUST replay keeps the root target through run101`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("two uniform main",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val make=p.method("two uniform make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.LocalVar(0);val b=AccessPathBase.LocalVar(1)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val r=AccessPathBase.LocalVar(4)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val t=MarkSlot.Concrete(p.mark("T"));val u=MarkSlot.Concrete(p.mark("U"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT,PathFact(a,listOf(ff),Tail.ANY_TAINT,t),ExclusionSet.Empty),
                PathEdge(ZERO_FACT,PathFact(b,emptyList(),Tail.ANY_TAINT,t),ExclusionSet.Empty)),
                StatementSummary.EMPTY,emptyList()))
            val builder=RulePredicate.Builder(f.cancellation)
            val predicate=builder.build(builder.leaf(p.pattern(arg,tail=Tail.ANY,mark=t)))
            val id=RuleOccurrenceId(FormKey(FormOwner(),make.method,make,p.inst(make,2)),RuleKind.CALL_SOURCE,0)
            p.statement(make,1,MicroEdgeBuilder().apply { move(r,null) }.build())
            p.statement(make,2,StatementSummary(emptySet(),emptyList(),emptyList(),emptyMap(),sources=listOf(
                SourceRuleOccurrence(id,predicate,listOf(SourceAction(ActionId(id,ActionRole.SOURCE,0),
                    p.pattern(r,mark=u).fact))))))
            p.statement(make,3,MicroEdgeBuilder().apply { move(ret,r) }.build())
            fun call(from:AccessPathBase,to:AccessPathBase)=CallPlan(setOf(from,to),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Callees(ADDED,RETURNED,listOf(make)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,
                    starEdge(ret,emptyList(),to,emptyList()),starEdge(arg,emptyList(),from,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            p.call(main,1,call(b,x));p.call(main,2,call(a,y))
            val observations=listOf(x,y).mapIndexed { i,base -> SinkRule(f.rule("uniform observation $i"),0,
                listOf(p.pattern(base,mark=u)),emptyList()) }
            p.exit(main,3,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,observations),false,emptySet()))
            val report=f.driver(TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            println("TWO_UNIFORM latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("TWO_UNIFORM run=${run.runIndex} targets=${root.outgoingTargets.size}")
                if(run.runIndex in 3..8) actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("UNIFORM_REL ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertEquals(TERMINATION_BASELINE_LAST_RUN,report.end.run)
            assertEquals(EndReason.RUN_LIMIT,report.end.reason)
            assertEquals(2,report.entries.count { !it.provisional })
            assertTrue(f.results.all { result -> result.analyzers.single { it.key == main }
                .outgoingTargets.any { it.premise.isZero && it.target == Target.DemandTarget } })
            assertTrue(f.results.filter { it.runIndex >= 6 }.all { result ->
                result.analyzers.none { it.key == make }
            }, "The cycle no longer analyzes make; saved replay alone continues it")
            for (result in f.results.filter { it.runIndex % 2 == 0 }) {
                val hits = result.analyzers.single { it.key == main }.sourceHits
                    ?.occurrences()?.map { it.forward.to.base }?.toSet().orEmpty()
                println("PRODUCER_HITS run=${result.runIndex} bases=$hits")
                assertEquals(if (result.runIndex < 6) setOf(a, b) else setOf(a), hits,
                    "Only the field producer permission remains from run-6")
            }
            for (run in listOf(7,9)) {
                val rootFacts = f.processed.filter { it.run == run && it.method == main }
                    .flatMap { f.ops.leaves(it.delta.facts).toList() }
                println("ROOT_SOURCES run=$run b=${rootFacts.any { it.fact.base == b && it.fact.mark == t }} " +
                    "a=${rootFacts.any { it.fact.base == a && it.fact.mark == t }}")
                assertFalse(rootFacts.any { it.fact.base == b && it.fact.mark == t })
                assertTrue(rootFacts.any { it.fact.base == a && it.fact.mark == t })
            }
            val retained = f.records.byEntry(make, p.pattern(arg, tail = Tail.ANY_TAINT, mark = t))
                .filter { it.premise.mark == t && it.conclusion.base == ret }
                .map { it.premise.toPattern() }.toSet()
            assertEquals(setOf(p.pattern(arg, tail = Tail.ANY_TAINT, mark = t),
                p.pattern(arg, listOf(ff), Tail.ANY_TAINT, t)), retained)
            assertTrue(f.processed.all { row -> f.ops.leaves(row.delta.facts)
                .all { it.fact.path.size <= 1 } }, "No increasing field limit is used by this cycle")
        }
    }
}
