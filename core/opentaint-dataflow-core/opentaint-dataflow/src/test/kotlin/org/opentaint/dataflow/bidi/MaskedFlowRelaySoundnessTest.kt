package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Soundness diagnostic. All relevant selected C2 cells equal the current
 * native cells here. R31's disjoint cleaner branch and R32's STAR relay
 * guard are inactive. Production transfer/admission is unchanged. */
class MaskedFlowRelaySoundnessTest {
    private data class Result(val latest: Int, val normal: Int, val total: Int)
    private fun run(wrap: Boolean = true, clean: Boolean = true, depth: Int = 1, uniform: Boolean = false, selectedMark: Boolean = false): Result {
        DriverFixtures().use { f ->
            val p=f.program
            val main=p.method("masked FLOW main",listOf(listOf(1),listOf(2),emptyList()),2).key()
            val wrappers=List(if(wrap) depth else 0) { index -> p.method("masked FLOW wrapper $index",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key() }
            val helper=p.method("masked FLOW helper",listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val a=AccessPathBase.LocalVar(0);val r=AccessPathBase.LocalVar(1)
            val tmp=AccessPathBase.LocalVar(2);val arg=AccessPathBase.Argument(0);val ret=AccessPathBase.Return
            val ff=p.field("f");val t=p.mark("T");val u=MarkSlot.Concrete(if(selectedMark) t else p.mark("U"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT,PathFact(a,listOf(ff),if(uniform) Tail.ANY_TAINT else Tail.EXACT,u),ExclusionSet.Empty)),
                StatementSummary.EMPTY,emptyList()))
            p.statement(helper,1,MicroEdgeBuilder().apply { read(ret,arg,listOf(ff)) }.build())
            val keep=f.summary(ZERO_KEEP,keepEdge(ret),keepEdge(arg))
            // Synthetic rule action, no unresolved library transfer: the
            // UNRESOLVED stage is only the fixture's exact keep form.
            p.call(helper,2,CallPlan(setOf(ret,arg),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,keep),
                CallStage.Actions(BOUND,ADDED,if(clean)
                    listOf(CleanStep.Clean(Cleaner(ret,null,CleanReach.EXACT,t))) else emptyList()),
                CallStage.Edges(ADDED,RETURNED,UNRESOLVED,keep),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,keep)
            ),emptyList(),BEFORE,AFTER))
            fun call(callee:MethodKey,from:AccessPathBase,to:AccessPathBase)=CallPlan(setOf(from,to),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,
                    f.summary(ZERO_KEEP,starEdge(from,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()),
                CallStage.Callees(ADDED,RETURNED,listOf(callee)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,
                    starEdge(ret,emptyList(),to,emptyList()),starEdge(arg,emptyList(),from,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            for((index,wrapper) in wrappers.withIndex()) {
                p.call(wrapper,1,call(wrappers.getOrNull(index+1) ?: helper,arg,tmp))
                p.statement(wrapper,2,MicroEdgeBuilder().apply { move(ret,tmp) }.build())
            }
            p.call(main,1,call(wrappers.firstOrNull() ?: helper,a,r))
            p.exit(main,2,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,
                listOf(SinkRule(f.rule("masked FLOW observation"),0,
                    listOf(p.pattern(r,tail=Tail.EXACT,mark=u)),emptyList()))),false,emptySet()))
            val report=f.driver(FixedLimits(List(15) { maxOf(1,it) }),20.seconds,
                invokeRun={ config,owner,timeout ->
                    if(config.index==2 && clean) {
                        val probe=f.manager.factsOf(PathFact(ret,emptyList(),Tail.EXACT,MarkSlot.STAR),
                            ExclusionSet.Empty,Layer.NORMAL)
                        val initials=checkNotNull(config.demand).initials(helper,probe,config.admissionPolicy)
                        assertTrue(initials.any { it.layer==Layer.NORMAL &&
                            (it.initial as? InitialAp)?.toPattern()==p.pattern(ret,tail=Tail.EXACT,mark=MarkSlot.STAR) },
                            "FLOW handoff must clear mx from the selector before nested admission")
                    }
                    f.configs+=config
                    val handlers=RunMethodHandlers(MethodLocalServicesFactory(::RunMethodLocalServices),
                        MethodCallServicesFactory(::RunMethodCallServices))
                    RunManager(config,owner,handlers,quantum=1).run(timeout).also(f.results::add)
                },run1MarkMode=MarkMode.FULL).analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
            return Result(report.end.run,report.entries.count{!it.provisional},report.entries.size)
        }
    }
    @Test fun `FLOW handoff clears the mask and retains the nested unrelated mark`() {
        // A countermodel that keeps the cleaner mx on a demand row is invalid.
        assertEquals(Result(3,1,1),run())
    }
    @Test fun `the direct helper call learns the masked NORMAL relation`() {
        assertEquals(Result(3,1,1),run(wrap=false))
    }
    @Test fun `without the cleaner mask the nested call keeps the observation`() {
        assertEquals(Result(3,1,1),run(clean=false))
    }
    @Test fun `mask-free demand relays through bounded wrapper depths for exact and uniform inputs`() {
        for(depth in 1..6) for(uniform in listOf(false,true))
            assertEquals(Result(3,1,1),run(depth=depth,uniform=uniform))
    }

    @Test fun `clearing guidance mx never restores the actually cleaned concrete point`() {
        assertEquals(Result(3,0,0),run(selectedMark=true))
    }

}
