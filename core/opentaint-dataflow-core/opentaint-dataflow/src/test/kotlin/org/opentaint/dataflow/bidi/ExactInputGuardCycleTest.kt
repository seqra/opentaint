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
class ExactInputGuardCycleTest {
    @Test fun `three calls with an exact point marking retain the target in the native diagnostic`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("exact input root",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val make=p.method("exact input make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.Argument(0)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val z=AccessPathBase.LocalVar(4)
            val r=AccessPathBase.LocalVar(5)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val hh=p.field("h");val t=MarkSlot.Concrete(p.mark("T"));val u=MarkSlot.Concrete(p.mark("U"))
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
                sourceRule(2,listOf(ff,gg,gg),emptyList(),u,t),sourceRule(3,emptyList(),listOf(hh),u,t))))
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
            println("EXACT_INPUT_GUARD_OUTPUT latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("EXACT_INPUT_GUARD_OUTPUT run=${run.runIndex} targets=${root.outgoingTargets.size}")
                actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("EXACT_INPUT_GUARD_REL run=${run.runIndex} layer=${facts.layer} protected=${(facts as? TaintTree)?.nonSubsumable != null} ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
                }
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            println("EXACT_INPUT_GUARD_CAPTURE run=${report.end.run} reason=${report.end.reason} normal=${report.entries.count { !it.provisional }}")
            assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
            assertEquals(EndReason.RUN_LIMIT, report.end.reason)
            assertTrue(f.results.all { run -> run.analyzers.single { it.key == main }.outgoingTargets
                .any { it.premise.isZero && it.target == Target.DemandTarget } })
        }
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
