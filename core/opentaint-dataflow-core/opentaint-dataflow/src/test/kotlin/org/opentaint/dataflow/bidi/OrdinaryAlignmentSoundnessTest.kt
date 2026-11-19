package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.IncreasingLimits
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Native revisit of the old 165/884 reference diagnostics. Ordinary CFG
 * transfers only. No prototype admission, cut, write or replay adapter. */
class OrdinaryAlignmentSoundnessTest {
    private data class Result(val latest:Int,val normal:Int,val provisional:Int)
    private fun run(case:Int, exact:Boolean=true, minimal:Boolean=false):Result {
        DriverFixtures().use { f ->
            val p=f.program;val ff=p.field("f");val gg=p.field("g")
            val t=MarkSlot.Concrete(p.mark("T"));val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val x=AccessPathBase.LocalVar(0);val b=AccessPathBase.LocalVar(1);val c=AccessPathBase.LocalVar(2)
            val main=if(minimal) p.method("alignment minimal main",listOf(listOf(1),listOf(2),emptyList()),2).key() else p.method("alignment $case main",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val wrapper=if(case==165) p.method("alignment 165 wrapper",
                listOf(listOf(1),listOf(2),listOf(3),listOf(4),listOf(5),emptyList()),5).key()
                else p.method("alignment 884 wrapper",listOf(listOf(1,6),listOf(2),listOf(3),listOf(4),listOf(5),listOf(10),listOf(7),listOf(8),listOf(9),listOf(10),emptyList()),10).key()
            val choose=if(minimal) p.method("alignment minimal choose",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key() else if(case==165) p.method("alignment 165 choose",
                listOf(listOf(1,4),listOf(2),listOf(3),listOf(9),listOf(5),listOf(6),listOf(7),listOf(8),listOf(9),emptyList()),9).key()
                else p.method("alignment 884 choose",
                    listOf(listOf(1,4),listOf(2),listOf(3),listOf(9),listOf(5),listOf(6),listOf(7),listOf(8),listOf(9),emptyList()),9).key()
            fun read(owner:MethodKey,at:Int,to:AccessPathBase,from:AccessPathBase,path:List<Int>)=
                p.statement(owner,at,MicroEdgeBuilder().apply { read(to,from,path) }.build())
            fun move(owner:MethodKey,at:Int,to:AccessPathBase,from:AccessPathBase,path:List<Int> = emptyList())=
                p.statement(owner,at,MicroEdgeBuilder().apply { move(to,from,path) }.build())
            fun kill(owner:MethodKey,at:Int,base:AccessPathBase,path:List<Int>)=
                p.statement(owner,at,MicroEdgeBuilder().apply { write(base,path,weak=false,values=emptyList(),aliasPaths=emptyList()) }.build())
            fun call(owner:MethodKey,at:Int,callee:MethodKey,from:AccessPathBase,to:AccessPathBase)=
                p.call(owner,at,CallPlan(setOf(from,to),listOf(
                    CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                    CallStage.Actions(BOUND,ADDED,emptyList()),
                    CallStage.Callees(ADDED,RETURNED,listOf(callee)),
                    CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                    CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,
                        starEdge(ret,emptyList(),to,emptyList()),starEdge(arg,emptyList(),from,emptyList())))
                ),emptyList(),BEFORE,AFTER))
            if(case==165) {
                read(wrapper,1,x,arg,listOf(gg,gg));call(wrapper,2,choose,x,b)
                move(wrapper,3,c,b,listOf(gg));move(wrapper,4,ret,c,listOf(gg))
                read(choose,1,x,arg,listOf(ff));move(choose,2,ret,x,listOf(ff))
                if(!minimal) {
                    kill(choose,3,ret,listOf(gg))
                    kill(choose,4,arg,listOf(gg));read(choose,5,x,arg,listOf(ff,gg,ff))
                    move(choose,6,b,x,listOf(ff));move(choose,7,ret,b,listOf(ff));kill(choose,8,ret,listOf(ff))
                }
            } else {
                kill(wrapper,1,arg,listOf(ff,ff,gg));read(wrapper,2,x,arg,listOf(ff))
                move(wrapper,3,b,x,listOf(ff));move(wrapper,4,c,b,listOf(gg));call(wrapper,5,choose,c,ret)
                kill(wrapper,6,arg,listOf(gg,ff,ff));read(wrapper,7,x,arg,listOf(gg,ff))
                move(wrapper,8,b,x,listOf(gg));call(wrapper,9,choose,b,ret)
                read(choose,1,x,arg,listOf(gg,ff,gg));move(choose,2,b,x,listOf(gg));move(choose,3,ret,b,listOf(ff))
                kill(choose,4,arg,listOf(ff,gg,gg));read(choose,5,x,arg,listOf(gg,ff,gg))
                move(choose,6,b,x,listOf(gg));move(choose,7,ret,b,listOf(ff));kill(choose,8,ret,listOf(ff,gg,ff))
            }
            val input=if(case==165) listOf(gg) else listOf(ff,gg,gg)
            val observed=if(case==165) listOf(gg,gg,ff) else input
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,PathEdge(ZERO_FACT,
                PathFact(x,input,if(case==165) Tail.ANY_TAINT else Tail.EXACT,t),ExclusionSet.Empty)),StatementSummary.EMPTY,emptyList()))
            if(minimal) call(main,1,wrapper,x,c) else { call(main,1,wrapper,x,b);call(main,2,wrapper,b,c) }
            p.exit(main,if(minimal) 2 else 3,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,
                listOf(SinkRule(f.rule("alignment $case observation"),0,
                    listOf(p.pattern(c,if(exact) observed else emptyList(),if(exact) Tail.EXACT else Tail.ANY,t)),emptyList()))),false,emptySet()))
            val report=f.driver(IncreasingLimits,30.seconds,run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
            return Result(report.end.run,report.entries.count{!it.provisional},report.entries.count{it.provisional})
        }
    }
    @Test fun `old 165 region witness reaches its exact observed point`() {
        val r=run(165)
        assertEquals(1,r.normal)
        assertEquals(0,r.provisional)
    }
    @Test fun `old 884 point witness reaches its exact observed point`() {
        val r=run(884)
        assertEquals(1,r.normal)
        assertEquals(0,r.provisional)
    }
    @Test fun `old 165 broad observation exposes the current missed witness`() {
        val r=run(165,exact=false)
        // Diagnostic for the confirmed broad-observation loss.
        assertEquals(0,r.normal)
        assertEquals(0,r.provisional)
    }
    @Test fun `old 884 broad observation retains its concrete witness`() {
        val r=run(884,exact=false)
        assertEquals(1,r.normal)
        assertEquals(0,r.provisional)
    }

    @Test fun `one straight-line call without overwrites still loses the broad witness`() {
        val r=run(165,exact=false,minimal=true)
        assertEquals(Result(5,0,0),r)
    }
    @Test fun `a named observation keeps the one-call witness`() {
        val r=run(165,exact=true,minimal=true)
        assertEquals(Result(5,1,0),r)
    }

    @Test fun `same-direction STAR replay cannot use the deeper saved premise`() {
        val f=StoreFixtures();val ff=f.field("f");val ret=AccessPathBase.Return
        val pattern=f.pattern(ret,listOf(ff),Tail.STAR,MarkSlot.STAR)
        val star=f.fact(ret,tail=Tail.STAR,mark=MarkSlot.STAR)
        val mode=ApMode(false,Direction.BACKWARD,3)
        assertNull(f.ops.satisfying(star,pattern,mode,record=true,role=SummaryReadRole.SAVED_DIRECT))
        assertNotNull(f.ops.satisfying(star,pattern,mode,record=true,role=SummaryReadRole.SAVED_OPPOSITE))
        val may=f.fact(ret,tail=Tail.ANY,mark=MarkSlot.STAR,layer=Layer.DEMAND)
        assertNotNull(f.ops.satisfying(may,pattern,mode,record=true,role=SummaryReadRole.SAVED_DIRECT))
    }

}
