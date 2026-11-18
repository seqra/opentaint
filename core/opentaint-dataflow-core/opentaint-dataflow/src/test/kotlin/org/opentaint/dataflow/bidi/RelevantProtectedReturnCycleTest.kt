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

/** Synthetic two-rule leaf body, three acyclic calls, no cleaner/pass/opaque code.
 * Native components are unchanged. Latest-proposal uncapped recurrence is proved in Lean;
 * the native run-101 diagnostic is not a proof that the proposal is installed. */
class RelevantProtectedReturnCycleTest {
    @Test fun `same-mark fresh result fields retain the finite native demand cycle`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("relevant protected root",listOf(listOf(1),listOf(2),listOf(3),listOf(4),listOf(5),listOf(6),listOf(7),emptyList()),7).key()
            val make=p.method("relevant protected make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.Argument(0)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val z=AccessPathBase.LocalVar(4)
            val r=AccessPathBase.LocalVar(5);val tmp=AccessPathBase.LocalVar(6)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val hh=p.field("h");val t=MarkSlot.Concrete(p.mark("T"))
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
                sourceRule(0,listOf(ff,gg,gg),listOf(hh),t,t),
                sourceRule(1,emptyList(),listOf(hh,hh),t,t))))
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
                listOf(p.pattern(z,tail=Tail.ANY,mark=t)),emptyList()))
            p.exit(main,7,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,observations),false,emptySet()))
            val report=f.driver(TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            println("RELEVANT_PROTECTED_RETURN_OUTPUT latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("RELEVANT_PROTECTED_RETURN_OUTPUT run=${run.runIndex} targets=${root.outgoingTargets.size}")
                actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("RELEVANT_PROTECTED_RETURN_REL run=${run.runIndex} layer=${facts.layer} protected=${(facts as? TaintTree)?.nonSubsumable != null} ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            println("RELEVANT_PROTECTED_RETURN_CAPTURE run=${report.end.run} reason=${report.end.reason} normal=${report.entries.count { !it.provisional }}")
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertTrue(f.results.all { run -> run.analyzers.single { it.key == main }.outgoingTargets
                .any { it.premise.isZero && it.target == Target.DemandTarget } })
        }
    }

    private class Out:ApOut {
        val values=arrayListOf<Facts>()
        override fun result(f:Facts) { values+=f }
        override fun markRequest(mark:TaintMark)=error("Unexpected request")
    }
    @Test fun `same mark assignment to a fresh h descendant stays NORMAL and protected`() {
        val f=StoreFixtures();val p=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
        val ff=f.field("f");val gg=f.field("g");val hh=f.field("h")
        val t=MarkSlot.Concrete(f.mark("T"))
        val initial=f.pattern(p,listOf(ff,gg),Tail.EXACT,t)
        val edge=PathEdge(f.pattern(p,tail=Tail.ANY,mark=t).fact,
            f.pattern(ret,listOf(hh,hh),Tail.ANY_TAINT,t).fact,ExclusionSet.Empty)
        val out=Out()
        f.ops.applyEdge(f.fact(p,listOf(ff,gg),Tail.EXACT,t),f.manager.initial(initial),edge,false,
            ApMode(false,Direction.FORWARD,8),out,ruleAssignment=true)
        assertTrue(out.values.isNotEmpty())
        assertTrue(out.values.all { it.layer==Layer.NORMAL && (it as TaintTree).nonSubsumable!=null })
        assertEquals(setOf(f.pattern(ret,listOf(hh,hh),Tail.ANY_TAINT,t)),
            out.values.flatMap { f.ops.leaves(it).toList() }.toSet())
        // H is an independent literal membership. It does not turn NORMAL into DEMAND.
        val bodyClosed=out.values.all { it.layer==Layer.NORMAL && (it as TaintTree).nonSubsumable==null }
        assertFalse(bodyClosed)
        val pass=Out()
        f.ops.applyEdge(f.fact(p,listOf(ff,gg),Tail.EXACT,t),f.manager.initial(initial),edge,false,
            ApMode(false,Direction.FORWARD,8),pass,ruleAssignment=false)
        assertTrue(pass.values.isNotEmpty())
        assertTrue(pass.values.all { (it as TaintTree).nonSubsumable==null })
    }
    @Test fun `C5 admits a protected NORMAL result in the same region as coarse demand`() {
        val f=StoreFixtures();val p=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
        val ff=f.field("f");val gg=f.field("g");val hh=f.field("h")
        val t=MarkSlot.Concrete(f.mark("T"))
        val initial=f.pattern(p,listOf(ff,gg),Tail.EXACT,t)
        val out=Out()
        f.ops.applyEdge(f.fact(p,listOf(ff,gg),Tail.EXACT,t),f.manager.initial(initial),
            PathEdge(f.pattern(p,tail=Tail.ANY,mark=t).fact,
                f.pattern(ret,listOf(hh,hh),Tail.ANY_TAINT,t).fact,ExclusionSet.Empty),
            false,ApMode(false,Direction.FORWARD,8),out,ruleAssignment=true)
        val demand=org.opentaint.dataflow.bidi.store.DemandStore.Builder(f.manager).apply {
            add(f.method,DemandPattern(f.pattern(p,listOf(ff),Tail.ANY,t),
                f.pattern(ret,listOf(hh),Tail.STAR,t)))
        }.build()
        val policy=RestrictedInitialPolicy(5,8)
        assertTrue(out.values.isNotEmpty())
        assertTrue(out.values.all { it.layer==Layer.NORMAL && (it as TaintTree).nonSubsumable!=null })
        assertTrue(out.values.all { value ->
            demand.intersect(f.method,f.manager.initial(initial),value,policy).isNotEmpty()
        })
    }
}
