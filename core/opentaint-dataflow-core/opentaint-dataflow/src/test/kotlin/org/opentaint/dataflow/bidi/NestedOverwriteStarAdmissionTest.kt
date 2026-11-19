package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Cold protocol adapter for the historical rejection and proposed run-2 relay.
 * It changes the old emitter's inner DATA start only in the traced cell;
 * saved replay, subscriptions, ZERO, transfers, C5 and the driver are native.
 * Production admission is unchanged. */
class NestedOverwriteStarAdmissionTest {
    private data class Result(val latest: Int, val findings: Int, val offered: List<Pattern>, val denied: Int, val relayed: Int)
    private fun run(selected: Boolean, wrap: Boolean = true, write: Boolean = true, relay: Boolean = false, markWritten: Boolean = false): Result {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("nested overwrite main",listOf(listOf(1),listOf(2),emptyList()),2).key()
            val wrapper=p.method("nested overwrite wrapper",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val inner=p.method("nested overwrite inner",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val a=AccessPathBase.LocalVar(0);val r=AccessPathBase.LocalVar(1)
            val tmp=AccessPathBase.LocalVar(2);val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val gg=p.field("g");val marked=if(markWritten) ff else gg;val t=MarkSlot.Concrete(p.mark("T"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT,PathFact(a,listOf(marked),Tail.EXACT,t),ExclusionSet.Empty)),
                StatementSummary.EMPTY,emptyList()))
            if(write) p.statement(inner,1,MicroEdgeBuilder().apply {
                write(arg,listOf(ff),weak=false,values=emptyList(),aliasPaths=emptyList())
            }.build())
            p.statement(inner,2,MicroEdgeBuilder().apply { move(ret,arg) }.build())
            fun call(callee:MethodKey,from:AccessPathBase,to:AccessPathBase)=CallPlan(setOf(from,to),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Callees(ADDED,RETURNED,listOf(callee)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,
                    starEdge(ret,emptyList(),to,emptyList()),starEdge(arg,emptyList(),from,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            p.call(wrapper,1,call(inner,arg,tmp))
            p.statement(wrapper,2,MicroEdgeBuilder().apply { move(ret,tmp) }.build())
            p.call(main,1,call(if(wrap) wrapper else inner,a,r))
            p.exit(main,2,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,
                listOf(SinkRule(f.rule("nested overwrite observation"),0,
                    listOf(p.pattern(r,listOf(marked),Tail.EXACT,t)),emptyList()))),false,emptySet()))
            val offers=arrayListOf<Pattern>();var denied=0;var relayed=0
            val actual=RunMethodHandlers(MethodLocalServicesFactory(::RunMethodLocalServices),
                MethodCallServicesFactory(::RunMethodCallServices))
            val driver=f.driver(FixedLimits(listOf(1,1,2,3,4,5,6)),20.seconds,
                invokeRun={ config,owner,timeout ->
                    val factory=RunnerHandlerFactory<RunMethodAnalyzer> { port ->
                        actual.create(object : RunnerPort<RunMethodAnalyzer> by port {
                            override fun startInitials(callee:MethodKey,initials:Collection<AdmittedInitial>) {
                                val keep=if(selected && wrap && config.index==2 && callee==inner)
                                    initials.mapNotNull { initial ->
                                        if(initial.initial.isZero) initial else {
                                            val key=initial.initial as InitialAp
                                            check(key.base==ret && key.path==null && key.tail==Tail.EXACT && key.mark==MarkSlot.STAR) {
                                                "The adapter changes only the old emitter's witnessed same-head STAR/FLOW cell: $key"
                                            }
                                            if(relay) {
                                                relayed++
                                                AdmittedInitial(f.manager.initial(p.pattern(ret,emptyList(),Tail.STAR,MarkSlot.STAR)),Layer.NORMAL)
                                            } else { denied++;null }
                                        }
                                    } else initials
                                port.startInitials(callee,keep)
                            }
                            override fun subscribe(sub:Subscription) {
                                if(config.index==2 && sub.callee==inner && !sub.zeroOnly)
                                    offers+=f.ops.leaves(sub.added).toList()
                                port.subscribe(sub)
                            }
                        })
                    }
                    f.configs+=config
                    RunManager(config,owner,factory,quantum=1).run(timeout).also(f.results::add)
                },run1MarkMode=MarkMode.FULL)
            val report=driver.analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
            if(selected && !relay && wrap && write) assertTrue(report.entries.isEmpty(), "The selected policy loses the entire observation")
            return Result(report.end.run,report.entries.count{!it.provisional},offers,denied,relayed)
        }
    }
    @Test fun `same-head STAR rejection can lose the nested write-through observation`() {
        val baseline=run(selected=false)
        val selected=run(selected=true)
        assertEquals(1,baseline.findings)
        assertEquals(3,baseline.latest)
        assertEquals(0,selected.findings)
        assertEquals(3,selected.latest)
        assertEquals(1,selected.denied)
        assertTrue(selected.offered.isNotEmpty())
        assertTrue(selected.offered.all { it.fact.path.isEmpty() && it.fact.tail==Tail.STAR })
    }
    @Test fun `the direct run2 deeper input still obtains the NORMAL provider`() {
        val direct=run(selected=true,wrap=false)
        assertEquals(1,direct.findings)
        assertEquals(3,direct.latest)
        assertEquals(0,direct.denied)
    }
    @Test fun `saved NORMAL replay handles the same nested route without a write`() {
        val plain=run(selected=true,write=false)
        assertEquals(1,plain.findings)
        assertEquals(1,plain.latest)
    }
    @Test fun `run2 STAR relay learns a NORMAL exclusion-guarded provider`() {
        val repaired=run(selected=true,relay=true)
        assertEquals(1,repaired.findings)
        assertEquals(3,repaired.latest)
        assertEquals(0,repaired.denied)
        assertEquals(1,repaired.relayed)
        assertTrue(repaired.offered.isNotEmpty())
        assertTrue(repaired.offered.all { it.fact.path.isEmpty() && it.fact.tail==Tail.STAR })
    }

    @Test fun `run2 relay preserves the strong-write exclusion for the overwritten point`() {
        val killed=run(selected=true,relay=true,markWritten=true)
        assertEquals(0,killed.findings)
        assertEquals(3,killed.latest)
        assertEquals(0,killed.denied)
        assertEquals(1,killed.relayed)
    }

}
