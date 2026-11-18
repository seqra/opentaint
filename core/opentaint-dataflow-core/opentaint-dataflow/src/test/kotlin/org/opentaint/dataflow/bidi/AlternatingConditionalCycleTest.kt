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
import org.opentaint.dataflow.bidi.store.FlowBackedSummaries
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Synthetic conditional generators and three acyclic calls. Production is unchanged.
 * Run-101 is a diagnostic capture; the uncapped Lean recurrence is the proof. */
class AlternatingConditionalCycleTest {
    @Test fun `three alternating conditional calls keep the synthetic target`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("alternating root",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val make=p.method("alternating make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.Argument(0)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val z=AccessPathBase.LocalVar(4)
            val r=AccessPathBase.LocalVar(5)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val t=MarkSlot.Concrete(p.mark("T"));val u=MarkSlot.Concrete(p.mark("U"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT,PathFact(a,listOf(ff),Tail.ANY_TAINT,t),ExclusionSet.Empty)),
                StatementSummary.EMPTY,emptyList()))
            fun sourceRule(ordinal: Int, conditionPath: List<Int>, targetPath: List<Int>, inputMark: MarkSlot.Concrete, outputMark: MarkSlot.Concrete): SourceRuleOccurrence {
                val builder=RulePredicate.Builder(f.cancellation)
                val predicate=builder.build(builder.leaf(p.pattern(arg, conditionPath, Tail.ANY, inputMark)))
                val id=RuleOccurrenceId(FormKey(FormOwner(),make.method,make,p.inst(make,2)),RuleKind.CALL_SOURCE,ordinal)
                return SourceRuleOccurrence(id,predicate,listOf(SourceAction(ActionId(id,ActionRole.SOURCE,0),
                    p.pattern(r,targetPath,Tail.ANY_TAINT,outputMark).fact)))
            }
            p.statement(make,1,MicroEdgeBuilder().apply { move(r,null) }.build())
            p.statement(make,2,StatementSummary(emptySet(),emptyList(),emptyList(),emptyMap(),sources=listOf(
                sourceRule(0,listOf(ff,gg),emptyList(),t,u),sourceRule(1,emptyList(),listOf(ff),t,u),
                sourceRule(2,listOf(ff,gg),emptyList(),u,t),sourceRule(3,emptyList(),listOf(ff),u,t))))
            p.statement(make,3,MicroEdgeBuilder().apply { move(ret,r) }.build())
            fun call(from:AccessPathBase,to:AccessPathBase)=CallPlan(setOf(from,to),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Callees(ADDED,RETURNED,listOf(make)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,
                    starEdge(ret,emptyList(),to,emptyList()),starEdge(arg,emptyList(),from,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            p.call(main,1,call(a,x));p.call(main,2,call(x,y));p.call(main,3,call(y,z))
            val observations=listOf(SinkRule(f.rule("alternating observation"),0,
                listOf(p.pattern(z,tail=Tail.ANY,mark=u)),emptyList()))
            p.exit(main,4,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,observations),false,emptySet()))
            val report=f.driver(TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            println("ALTERNATING_OUTPUT latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("ALTERNATING_OUTPUT run=${run.runIndex} targets=${root.outgoingTargets.size}")
                actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("ALTERNATING_REL run=${run.runIndex} layer=${facts.layer} protected=${(facts as? TaintTree)?.nonSubsumable != null} ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            println("ALTERNATING_CAPTURE run=${report.end.run} reason=${report.end.reason} normal=${report.entries.count { !it.provisional }}")
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertTrue(f.results.all { run -> run.analyzers.single { it.key == main }.outgoingTargets
                .any { it.premise.isZero && it.target == Target.DemandTarget } })
        }
    }

    private class Applied : ApOut {
        val values = arrayListOf<Facts>()
        override fun result(f: Facts) { values += f }
        override fun markRequest(mark: TaintMark) = error("Unexpected mark request")
    }

    @Test fun `native conditional generators have the two claimed distinct outputs`() {
        val s = StoreFixtures()
        val arg = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
        val ff = s.field("f"); val gg = s.field("g")
        val t = MarkSlot.Concrete(s.mark("T")); val u = MarkSlot.Concrete(s.mark("U"))
        for ((inputMark,outputMark) in listOf(t to u,u to t)) {
            for (path in listOf(emptyList(),listOf(ff))) {
                val input = s.fact(arg,path,Tail.STAR,inputMark,layer=Layer.DEMAND)
                val initial = s.manager.initial(s.pattern(arg,path,Tail.STAR,inputMark))
                val rootRule = PathEdge(s.pattern(arg,listOf(ff,gg),Tail.ANY,inputMark).fact,
                    s.pattern(ret,tail=Tail.ANY_TAINT,mark=outputMark).fact,ExclusionSet.Empty)
                val fieldRule = PathEdge(s.pattern(arg,tail=Tail.ANY,mark=inputMark).fact,
                    s.pattern(ret,listOf(ff),Tail.ANY_TAINT,outputMark).fact,ExclusionSet.Empty)
                for ((edge,expected) in listOf(rootRule to s.pattern(ret,tail=Tail.ANY,mark=outputMark),
                    fieldRule to s.pattern(ret,listOf(ff),Tail.ANY_TAINT,outputMark))) {
                    val out=Applied()
                    s.ops.applyEdge(input,initial,edge,true,ApMode(false,Direction.FORWARD,8),out,
                        ruleAssignment=true)
                    assertEquals(setOf(expected),out.values.flatMap { s.ops.leaves(it).toList() }.toSet())
                    assertTrue(out.values.all { it.layer==Layer.DEMAND })
                    assertTrue(out.values.all { (it as? TaintTree)?.nonSubsumable==null })
                }
            }
        }
    }

    @Test fun `FLOW coverage removes diagonal demand but keeps both cross mark witnesses in either order`() {
        val s=StoreFixtures();val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
        val t=MarkSlot.Concrete(s.mark("T"));val u=MarkSlot.Concrete(s.mark("U"))
        for (flowFirst in listOf(false,true)) {
            val store=FlowBackedSummaries(s.manager)
            val flowP=s.manager.initial(s.pattern(arg,tail=Tail.STAR,mark=MarkSlot.STAR))
            val tP=s.manager.initial(s.pattern(arg,tail=Tail.STAR,mark=t))
            val uP=s.manager.initial(s.pattern(arg,tail=Tail.STAR,mark=u))
            val flow=s.fact(ret,tail=Tail.ANY,mark=MarkSlot.STAR,layer=Layer.DEMAND)
            fun marked() {
                store.addAll(tP,s.fact(ret,tail=Tail.ANY,mark=t,layer=Layer.DEMAND))
                store.addAll(tP,s.fact(ret,tail=Tail.ANY,mark=u,layer=Layer.DEMAND))
                store.addAll(uP,s.fact(ret,tail=Tail.ANY,mark=t,layer=Layer.DEMAND))
            }
            if(flowFirst) store.addAll(flowP,flow)
            marked()
            if(!flowFirst) store.addAll(flowP,flow)
            assertEquals(setOf(s.pattern(ret,tail=Tail.ANY,mark=u)),
                store.borrow(tP).flatMap { s.ops.leaves(it) }.toSet())
            assertEquals(setOf(s.pattern(ret,tail=Tail.ANY,mark=t)),
                store.borrow(uP).flatMap { s.ops.leaves(it) }.toSet())
        }
    }
}
