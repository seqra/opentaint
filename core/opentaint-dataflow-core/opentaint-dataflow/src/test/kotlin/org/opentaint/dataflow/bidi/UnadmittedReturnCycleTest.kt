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
class UnadmittedReturnCycleTest {
    @Test fun `a third checked mark retains the target in the unchanged native diagnostic`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("unadmitted return root",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val make=p.method("unadmitted return make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.Argument(0)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val z=AccessPathBase.LocalVar(4)
            val r=AccessPathBase.LocalVar(5)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val hh=p.field("h");val kk=p.field("k");val ss=p.field("s");val t=MarkSlot.Concrete(p.mark("T"));val u=MarkSlot.Concrete(p.mark("U"));val v=MarkSlot.Concrete(p.mark("V"))
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
                sourceRule(0,listOf(ff,gg,gg),emptyList(),t,u),sourceRule(1,emptyList(),listOf(hh),t,u),
                sourceRule(2,listOf(ff,gg,gg),emptyList(),u,t),sourceRule(3,emptyList(),listOf(hh),u,t),
                sourceRule(4,emptyList(),listOf(kk),t,v),sourceRule(5,listOf(ss),listOf(hh),v,u))))
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
            println("UNADMITTED_RETURN_OUTPUT latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("UNADMITTED_RETURN_OUTPUT run=${run.runIndex} targets=${root.outgoingTargets.size}")
                actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("UNADMITTED_RETURN_REL run=${run.runIndex} layer=${facts.layer} protected=${(facts as? TaintTree)?.nonSubsumable != null} ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            println("UNADMITTED_RETURN_CAPTURE run=${report.end.run} reason=${report.end.reason} normal=${report.entries.count { !it.provisional }}")
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertTrue(f.results.all { run -> run.analyzers.single { it.key == main }.outgoingTargets
                .any { it.premise.isZero && it.target == Target.DemandTarget } })
        }
    }

    @Test fun `a normal return effect can be outside every relevant paired C5 output`() {
        val f=StoreFixtures()
        val p=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
        val ff=f.field("f");val gg=f.field("g");val hh=f.field("h");val kk=f.field("k");val ss=f.field("s")
        val t=MarkSlot.Concrete(f.mark("T"));val u=MarkSlot.Concrete(f.mark("U"));val v=MarkSlot.Concrete(f.mark("V"))
        val initial=f.pattern(p,listOf(ff,gg),Tail.EXACT,t)
        val output=f.fact(ret,listOf(kk),Tail.ANY_TAINT,v)
        assertEquals(Layer.NORMAL,output.layer)
        val demand=org.opentaint.dataflow.bidi.store.DemandStore.Builder(f.manager).apply {
            add(f.method,DemandPattern(
                f.pattern(p,listOf(ff),Tail.ANY,t),f.pattern(ret,tail=Tail.STAR,mark=u)))
            add(f.method,DemandPattern(
                f.pattern(p,listOf(ff),Tail.ANY,t),f.pattern(ret,listOf(hh),Tail.EXACT,u)))
        }.build()
        val policy=RestrictedInitialPolicy(3,8)
        assertTrue(policy.emitAdmissions(f.pattern(p,listOf(ff),Tail.ANY,t),initial,Layer.NORMAL)
            .any { it.pattern==initial && it.layer==Layer.NORMAL })
        val admitted=demand.intersect(f.method,f.manager.initial(initial),output,policy)
        assertTrue(admitted.isEmpty())
        // V is not dead at the provider boundary: a literal CM(p.s,V) action consumes V.
        // Its input region is disjoint from the produced k region.
        val condition=PathEdge(f.pattern(p,listOf(ss),Tail.ANY,v).fact,
            f.pattern(ret,listOf(hh),Tail.ANY_TAINT,u).fact,ExclusionSet.Empty)
        val applied=Applied()
        f.ops.applyEdge(f.fact(p,listOf(kk),Tail.ANY_TAINT,v),
            f.manager.initial(f.pattern(p,listOf(kk),Tail.ANY_TAINT,v)),condition,false,
            ApMode(false,Direction.FORWARD,8),applied,ruleAssignment=true)
        assertTrue(applied.values.isEmpty())
        val coarsePattern=f.pattern(p,tail=Tail.STAR,mark=v)
        val possible=Applied()
        f.ops.applyEdge(f.fact(p,tail=Tail.STAR,mark=v,layer=Layer.DEMAND),
            f.manager.initial(coarsePattern),condition,false,
            ApMode(false,Direction.FORWARD,8),possible,ruleAssignment=true)
        assertEquals(setOf(f.pattern(ret,listOf(hh),Tail.ANY,u)),
            possible.values.flatMap { f.ops.leaves(it).toList() }.toSet())
        assertTrue(possible.values.all { it.layer==Layer.DEMAND })
    }

    private class Applied : ApOut {
        val values = arrayListOf<Facts>()
        override fun result(f: Facts) { values += f }
        override fun markRequest(mark: TaintMark) = error("Unexpected request")
    }

    @Test fun `an exact input has no deep guard match but its first field start does`() {
        val s = StoreFixtures()
        val p = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
        val ff = s.field("f"); val gg = s.field("g"); val hh = s.field("h")
        val t = MarkSlot.Concrete(s.mark("T")); val u = MarkSlot.Concrete(s.mark("U"))
        val actual = s.pattern(p, listOf(ff, gg), Tail.EXACT, t)
        val admission = RestrictedInitialPolicy(5, 8).emitAdmissions(s.pattern(p, tail = Tail.ANY, mark = t), actual, Layer.NORMAL)
        assertTrue(admission.any { it.pattern == s.pattern(p, listOf(ff), Tail.STAR, t) && it.layer == Layer.DEMAND })
        // Both latest real-E repairs are ineligible: this is EXACT with Empty E.
        assertEquals(ExclusionSet.Empty, actual.exclusion)
        assertEquals(Tail.EXACT, actual.fact.tail)
        val guard = PathEdge(s.pattern(p, listOf(ff, gg, gg), Tail.ANY, t).fact,
            s.pattern(ret, tail = Tail.ANY_TAINT, mark = u).fact, ExclusionSet.Empty)
        val fine = Applied()
        s.ops.applyEdge(s.fact(p, listOf(ff, gg), Tail.EXACT, t), s.manager.initial(actual), guard, false,
            ApMode(false, Direction.FORWARD, 8), fine, ruleAssignment = true)
        assertTrue(fine.values.isEmpty())
        val coarse = Applied()
        val q = s.pattern(p, listOf(ff), Tail.STAR, t)
        s.ops.applyEdge(s.fact(p, listOf(ff), Tail.STAR, t, layer = Layer.DEMAND), s.manager.initial(q), guard, false,
            ApMode(false, Direction.FORWARD, 8), coarse, ruleAssignment = true)
        assertEquals(setOf(s.pattern(ret, tail = Tail.ANY, mark = u)), coarse.values.flatMap { s.ops.leaves(it).toList() }.toSet())
        assertTrue(coarse.values.all { it.layer == Layer.DEMAND })
        val replies = arrayListOf<Facts>()
        val out = object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) { replies += value }
            override fun target(original: PremiseKey, target: Target) = error("Unexpected terminal")
            override fun markRequest(mark: TaintMark) = error("Unexpected request")
        }
        LocalRelationApplication(s.ops, ApMode(false, Direction.FORWARD, 8)).applyCurrent(
            s.fact(p, listOf(ff, gg), Tail.EXACT, t), s.manager.zero, s.manager.initial(q),
            s.fact(ret, tail = Tail.ANY, mark = u, layer = Layer.DEMAND), out)
        assertEquals(setOf(s.pattern(ret, tail = Tail.ANY, mark = u)), replies.flatMap { s.ops.leaves(it).toList() }.toSet())
        assertTrue(replies.all { it.layer == Layer.DEMAND })
        assertFalse(covers(s.pattern(ret, listOf(hh), Tail.ANY_TAINT, u), s.pattern(ret, tail = Tail.ANY, mark = u)))
    }
}
