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

/** Synthetic six-rule leaf body, three acyclic calls, no cleaner/pass/opaque code.
 * Native components are unchanged. Latest-proposal uncapped recurrence is proved in Lean;
 * the native run-101 diagnostic is not a proof that the proposal is installed. */
class UnadmittedFieldCycleTest {
    @Test fun `a same mark disjoint return retains the target through ordinary field reads`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("unadmitted field root",listOf(listOf(1),listOf(2),listOf(3),listOf(4),listOf(5),listOf(6),listOf(7),emptyList()),7).key()
            val make=p.method("unadmitted field make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.Argument(0)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val z=AccessPathBase.LocalVar(4)
            val r=AccessPathBase.LocalVar(5);val tmp=AccessPathBase.LocalVar(6)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val hh=p.field("h");val kk=p.field("k");val t=MarkSlot.Concrete(p.mark("T"));val u=MarkSlot.Concrete(p.mark("U"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT,PathFact(a,listOf(ff,gg),Tail.EXACT,t),ExclusionSet.Empty)),
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
                sourceRule(0,listOf(ff,gg,gg),listOf(hh),t,u),sourceRule(1,emptyList(),listOf(hh,hh),t,u),
                sourceRule(2,emptyList(),listOf(kk),t,u),
                sourceRule(3,listOf(ff,gg,gg),listOf(hh),u,t),sourceRule(4,emptyList(),listOf(hh,hh),u,t),
                sourceRule(5,emptyList(),listOf(kk),u,t))))
            p.statement(make,3,MicroEdgeBuilder().apply { move(ret,r) }.build())
            fun call(from:AccessPathBase,to:AccessPathBase)=CallPlan(setOf(from,to),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Callees(ADDED,RETURNED,listOf(make)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,
                    starEdge(ret,emptyList(),to,emptyList()),starEdge(arg,emptyList(),from,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            p.call(main,1,call(a,tmp));p.statement(main,2,MicroEdgeBuilder().apply { read(x,tmp,listOf(hh)) }.build())
            p.call(main,3,call(x,tmp));p.statement(main,4,MicroEdgeBuilder().apply { read(y,tmp,listOf(hh)) }.build())
            p.call(main,5,call(y,tmp));p.statement(main,6,MicroEdgeBuilder().apply { read(z,tmp,listOf(hh)) }.build())
            val observations=listOf(SinkRule(f.rule("alternating observation"),0,
                listOf(p.pattern(z,tail=Tail.ANY,mark=u)),emptyList()))
            p.exit(main,7,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,observations),false,emptySet()))
            val report=f.driver(TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            println("UNADMITTED_FIELD_OUTPUT latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("UNADMITTED_FIELD_OUTPUT run=${run.runIndex} targets=${root.outgoingTargets.size}")
                actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("UNADMITTED_FIELD_REL run=${run.runIndex} layer=${facts.layer} protected=${(facts as? TaintTree)?.nonSubsumable != null} ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            println("UNADMITTED_FIELD_CAPTURE run=${report.end.run} reason=${report.end.reason} normal=${report.entries.count { !it.provisional }}")
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertTrue(f.results.all { run -> run.analyzers.single { it.key == main }.outgoingTargets
                .any { it.premise.isZero && it.target == Target.DemandTarget } })
        }
    }

    @Test fun `paired C5 admits hh but rejects k of the same output mark`() {
        val f=StoreFixtures()
        val p=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
        val ff=f.field("f");val gg=f.field("g");val hh=f.field("h");val kk=f.field("k")
        val t=MarkSlot.Concrete(f.mark("T"));val u=MarkSlot.Concrete(f.mark("U"))
        val initial=f.pattern(p,listOf(ff,gg),Tail.EXACT,t)
        val demand=org.opentaint.dataflow.bidi.store.DemandStore.Builder(f.manager).apply {
            add(f.method,DemandPattern(f.pattern(p,listOf(ff),Tail.ANY,t),
                f.pattern(ret,listOf(hh),Tail.STAR,u)))
        }.build()
        val policy=RestrictedInitialPolicy(5,8)
        val accepted=demand.intersect(f.method,f.manager.initial(initial),f.fact(ret,listOf(hh,hh),Tail.ANY_TAINT,u),policy)
        val rejected=demand.intersect(f.method,f.manager.initial(initial),f.fact(ret,listOf(kk),Tail.ANY_TAINT,u),policy)
        assertTrue(accepted.isNotEmpty())
        assertTrue(rejected.isEmpty())
    }

    @Test fun `ordinary known prefix read keeps the coarse and fine results distinct`() {
        val f=StoreFixtures();val ret=AccessPathBase.Return;val x=AccessPathBase.LocalVar(1)
        val hh=f.field("h");val kk=f.field("k");val u=MarkSlot.Concrete(f.mark("U"))
        fun apply(path:List<Int>,tail:Tail,layer:Layer):List<Facts> {
            val result=arrayListOf<Facts>()
            val initial=f.pattern(ret,path,tail,u)
            f.ops.applyEdge(f.fact(ret,path,tail,u,layer=layer),f.manager.initial(initial),
                starEdge(ret,listOf(hh),x,emptyList()),false,ApMode(false,Direction.FORWARD,8),
                object:ApOut {
                    override fun result(f:Facts) { result+=f }
                    override fun markRequest(mark:TaintMark)=error("Unexpected request")
                })
            return result
        }
        val coarse=apply(listOf(hh),Tail.ANY,Layer.DEMAND)
        assertEquals(setOf(f.pattern(x,tail=Tail.ANY,mark=u)),coarse.flatMap { f.ops.leaves(it).toList() }.toSet())
        assertTrue(coarse.all { it.layer==Layer.DEMAND })
        val fine=apply(listOf(hh,hh),Tail.ANY_TAINT,Layer.NORMAL)
        assertEquals(setOf(f.pattern(x,listOf(hh),Tail.ANY_TAINT,u)),fine.flatMap { f.ops.leaves(it).toList() }.toSet())
        assertTrue(fine.all { it.layer==Layer.NORMAL })
        assertTrue(apply(listOf(kk),Tail.ANY_TAINT,Layer.NORMAL).isEmpty())
    }
}
