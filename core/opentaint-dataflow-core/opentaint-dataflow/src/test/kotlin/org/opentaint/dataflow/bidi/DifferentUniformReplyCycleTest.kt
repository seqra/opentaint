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
class DifferentUniformReplyCycleTest {
    private class Output : LocalRelationOut {
        val values = arrayListOf<Facts>()
        override fun data(original: PremiseKey, value: Facts) { values += value }
        override fun target(original: PremiseKey, target: Target) = error("Unexpected control")
        override fun markRequest(mark: TaintMark) = error("Unexpected request")
    }

    /** Test-only adapter for the consolidated identical EXACT/MUST support law.
     * One actual, empty E/mx, plain H, and one nonidentity return continuation. */
    private fun folded(f: StoreFixtures, values: List<Facts>): Set<Pair<Pattern, Layer>> {
        val packet = ConclusionGroup(f.manager, f.manager.newInterners())
        values.forEach { packet.addAll(it) }
        val all = packet.all().flatMap { fact -> f.ops.leaves(fact).map { it to fact.layer } }.toSet()
        val definiteNormal = all.filter { (p, l) -> l == Layer.NORMAL &&
            p.fact.mark is MarkSlot.Concrete && (p.fact.tail == Tail.ANY_TAINT ||
            p.fact.tail == Tail.EXACT && p.exclusion == ExclusionSet.Empty) }.map { it.first }.toSet()
        return all.filterNot { (p, l) -> l == Layer.DEMAND && p in definiteNormal }.toSet()
    }

    @Test fun `all additional exact and g guards still leave a different uniform demand reply`() {
        val f = StoreFixtures()
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val ff = f.field("f"); val gg = f.field("g")
        val t = MarkSlot.Concrete(f.mark("T")); val u = MarkSlot.Concrete(f.mark("U"))
        val actual = f.fact(arg, listOf(ff), Tail.ANY_TAINT, t)
        fun record(path: List<Int>, target: List<Int>, tail: Tail = Tail.ANY_TAINT) =
            Record(f.method, Direction.FORWARD,
                f.manager.initial(f.pattern(arg, path, Tail.ANY_TAINT, t)),
                f.fact(ret, target, tail, u))
        val records = listOf(record(listOf(gg), emptyList(), Tail.EXACT),
            record(listOf(gg), emptyList()), record(emptyList(), emptyList()),
            record(listOf(gg), listOf(ff), Tail.EXACT), record(emptyList(), listOf(ff), Tail.EXACT),
            record(listOf(ff), listOf(ff), Tail.EXACT), record(listOf(ff), listOf(ff)))
        val application = LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8))
        val expected = setOf(
            f.pattern(ret, tail = Tail.ANY_TAINT, mark = u) to Layer.DEMAND,
            f.pattern(ret, listOf(ff), Tail.EXACT, u) to Layer.NORMAL,
            f.pattern(ret, listOf(ff), Tail.ANY_TAINT, u) to Layer.NORMAL)
        for (order in listOf(records, records.reversed())) {
            val out = Output()
            for (r in order) application.applyRecord(actual, f.manager.zero, r, out)
            assertEquals(expected, folded(f, out.values))
            assertEquals(expected, folded(f, out.values.reversed()))
        }
        val withoutBroad = Output()
        for (r in records.filterIndexed { index, _ -> index != 2 })
            application.applyRecord(actual, f.manager.zero, r, withoutBroad)
        assertEquals(expected.filter { it.second == Layer.NORMAL }.toSet(),
            folded(f, withoutBroad.values), "Only the broad native record renews root DEMAND")
        for (r in listOf(records[0], records[1], records[3])) {
            val out = Output()
            assertFalse(application.applyRecord(actual, f.manager.zero, r, out))
            assertTrue(out.values.isEmpty(), "The more precise g guard cannot match f")
        }
        val current = Output()
        assertFalse(application.applyCurrent(actual, f.manager.zero, records[2].premise,
            records[2].conclusion, current))
        assertTrue(current.values.isEmpty())
    }

    @Test fun `reverse different uniform outputs select their real T input heads`() {
        val f = StoreFixtures()
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val ff = f.field("f")
        val t = MarkSlot.Concrete(f.mark("T")); val u = MarkSlot.Concrete(f.mark("U"))
        for (path in listOf(emptyList(), listOf(ff))) {
            val r = Record(f.method, Direction.FORWARD,
                f.manager.initial(f.pattern(arg, path, Tail.ANY_TAINT, t)),
                f.fact(ret, path, Tail.ANY_TAINT, u))
            val view = r.reversedAt(f.pattern(ret, tail = Tail.ANY, mark = u)).single()
            assertEquals(f.pattern(ret, path, Tail.STAR, u), view.premise)
            assertEquals(f.pattern(arg, path, Tail.ANY, t).fact, view.result.fact)
            assertTrue(view.result.demand)
        }
    }

    @Test fun `different uniform outputs keep root demand through run101`() {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("two uniform main",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val make=p.method("two uniform make",listOf(listOf(1),listOf(2),listOf(3),listOf(4),emptyList()),4).key()
            val a=AccessPathBase.LocalVar(0);val b=AccessPathBase.LocalVar(1)
            val x=AccessPathBase.LocalVar(2);val y=AccessPathBase.LocalVar(3)
            val r=AccessPathBase.LocalVar(4)
            val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val t=MarkSlot.Concrete(p.mark("T"));val u=MarkSlot.Concrete(p.mark("U"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT,PathFact(a,listOf(ff),Tail.ANY_TAINT,t),ExclusionSet.Empty),
                PathEdge(ZERO_FACT,PathFact(b,emptyList(),Tail.ANY_TAINT,t),ExclusionSet.Empty)),
                StatementSummary.EMPTY,emptyList()))
            fun sourceRule(ordinal: Int, conditionPath: List<Int>, targetPath: List<Int>): SourceRuleOccurrence {
                val builder=RulePredicate.Builder(f.cancellation)
                val predicate=builder.build(builder.leaf(p.pattern(arg, conditionPath, Tail.ANY, t)))
                val id=RuleOccurrenceId(FormKey(FormOwner(),make.method,make,p.inst(make,2)),RuleKind.CALL_SOURCE,ordinal)
                return SourceRuleOccurrence(id,predicate,listOf(SourceAction(ActionId(id,ActionRole.SOURCE,0),
                    p.pattern(r,targetPath,Tail.ANY_TAINT,u).fact)))
            }
            p.statement(make,1,MicroEdgeBuilder().apply { move(r,null) }.build())
            p.statement(make,2,StatementSummary(emptySet(),emptyList(),emptyList(),emptyMap(),sources=listOf(
                sourceRule(0,listOf(gg),emptyList()),sourceRule(1,emptyList(),listOf(ff)))))
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
                listOf(p.pattern(base,tail=Tail.ANY,mark=u)),emptyList()) }
            p.exit(main,3,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,observations),false,emptySet()))
            val report=f.driver(TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            println("MISMATCHED_OUTPUT latest=${report.end.run} reason=${report.end.reason}")
            for(run in f.results) {
                val actor=run.analyzers.singleOrNull{it.key==make}
                val root=run.analyzers.single{it.key==main}
                println("MISMATCHED_OUTPUT run=${run.runIndex} targets=${root.outgoingTargets.size}")
                if(run.runIndex in 1..10) actor?.summaries?.all()?.forEach { (initial,facts) ->
                    println("MISMATCHED_REL ${(initial as? InitialAp)?.toPattern()} -> ${f.ops.leaves(facts).toList()}")
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
            }, "No current make analysis remains; saved replay keeps the cycle alive")
            for (result in f.results.filter { it.runIndex % 2 == 0 }) {
                val hits = result.analyzers.single { it.key == main }.sourceHits
                    ?.occurrences()?.map { it.forward.to.base }?.toSet().orEmpty()
                println("UNIFORM_PRODUCER_HITS run=${result.runIndex} bases=$hits")
                assertEquals(if (result.runIndex < 6) setOf(a, b) else setOf(a), hits)
            }
            for (record in f.records.byEntry(make, p.pattern(arg, tail = Tail.ANY_TAINT, mark = t)))
                if (record.premise.mark == t && record.conclusion.base == ret)
                    println("RETAINED_MISMATCHED ${record.premise.toPattern()} -> ${f.ops.leaves(record.conclusion).toList()}")
            val retained = f.records.byEntry(make, p.pattern(arg, tail = Tail.ANY_TAINT, mark = t))
                .filter { it.premise.mark == t && it.conclusion.base == ret }
            assertEquals(setOf(p.pattern(arg, tail = Tail.ANY_TAINT, mark = t),
                p.pattern(arg, listOf(ff), Tail.ANY_TAINT, t)), retained.map { it.premise.toPattern() }.toSet())
            assertTrue(retained.all { record -> f.ops.leaves(record.conclusion).all {
                it.fact.tail == Tail.ANY_TAINT && record.conclusion.layer == Layer.NORMAL &&
                    it.fact.path == record.premise.toPattern().fact.path
            } })
            assertTrue(f.processed.all { row -> f.ops.leaves(row.delta.facts)
                .all { it.fact.path.size <= 1 } }, "No increasing field limit is used by this cycle")
        }
    }
}
