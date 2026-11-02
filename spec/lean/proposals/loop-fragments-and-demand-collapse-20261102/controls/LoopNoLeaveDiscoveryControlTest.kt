package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class LoopNoLeaveDiscoveryControlTest {
 @Test fun `FULL no leave loop uses existing backward exceptional discovery`() {
  DriverFixtures().use { f ->
   val p=f.program
   // B(p) { x=p; while(true) { sourceFF(x); x=x.f; sinkRootT(x); } }
   // 0 entry,1 x=p,2 loop test,3 sourceFF,4 read,5 sink,6 unreachable normal exit,7 discovery-only exceptional exit.
   val b=p.method("loop-no-leave-source-ff",listOf(listOf(1),listOf(2),listOf(3),listOf(4),listOf(5),listOf(2),emptyList(),emptyList()), normalExit=6, exceptionalExit=7, backwardExitDiscovery=true).key()
   val arg=AccessPathBase.Argument(0); val x=AccessPathBase.LocalVar(0)
   val fld=p.field("f");val t=MarkSlot.Concrete(p.mark("T"))
   p.statement(b,1,MicroEdgeBuilder().apply { move(x,arg) }.build())
   val source=PathEdge(ZERO_FACT,PathFact(x,listOf(fld,fld),Tail.EXACT,t),ExclusionSet.Empty)
   p.call(b,3,CallPlan(setOf(x),listOf(
    CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(keepEdge(x),ZERO_KEEP)),
    CallStage.Actions(BOUND,ADDED,emptyList()),
    CallStage.Edges(ADDED,RETURNED,SOURCES,f.summary(keepEdge(x),ZERO_KEEP,source)),
    CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
    CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(keepEdge(x),ZERO_KEEP))
   ),emptyList(),BEFORE,AFTER))
   p.statement(b,4,MicroEdgeBuilder().apply { read(x,x,listOf(fld)) }.build())
   val sink=SinkRule(f.rule("loop-root-sink"),0,listOf(p.pattern(x,mark=t)),emptyList())
   p.call(b,5,CallPlan(setOf(x),listOf(
    CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(keepEdge(x),ZERO_KEEP)),
    CallStage.Actions(BOUND,ADDED,emptyList()),
    CallStage.Edges(ADDED,RETURNED,UNRESOLVED,f.summary(keepEdge(x),ZERO_KEEP)),
    CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
    CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(keepEdge(x),ZERO_KEEP))
   ),listOf(sink),BEFORE,AFTER))
   val report=f.driver(FixedLimits(listOf(1,1,2,3,4,5,6)),15.seconds,run1MarkMode=MarkMode.FULL).analyze(listOf(b))
   fun desc(fact:PathFact)="${fact.base}:${fact.path.size}:${fact.tail}:${fact.mark}"
   println("CONTROL_END ${report.end} reports=${report.entries.size} runs=${f.configs.map{it.index}}")
   f.results.forEachIndexed { index,result ->
    for (actor in result.analyzers) {
     println("CONTROL_TARGET run=${index+1} raw="+actor.targets.map { row -> row.premise.members.map { it.toPattern() } to row.target })
     println("CONTROL_TARGET run=${index+1} outgoing="+actor.outgoingTargets.map { row -> row.premise.members.map { it.toPattern() } to row.target })
    }
   }
   for(row in f.processed) if(row.delta.node.location.index in listOf(3,4,5)) {
    val facts=f.ops.leaves(row.delta.facts).joinToString { desc(it.fact) }
    println("CONTROL_POINT run=${row.run} point=${row.delta.node.location.index} original=${row.delta.premise} layer=${row.delta.facts.layer} facts=$facts")
   }
   val demand2=f.configs.single { it.index==2 }.demand!!
   val rawFeedback=p.fact(x,listOf(fld),Tail.EXACT,t)
   val zero=f.manager.zero
   println("B_RUN2_DATA_ROWS "+demand2.explicitRows(b))
   println("B_RUN2_ZERO_C2 "+demand2.initials(b,Reach.NORMAL,f.configs[1].admissionPolicy))
   println("B_RUN2_TARGET_C5 "+demand2.acceptsTarget(b,zero,f.configs[1].admissionPolicy))
   println("B_C5_FEEDBACK accepts="+demand2.intersect(b,zero,rawFeedback,f.configs[1].admissionPolicy).size)
   assertTrue(demand2.intersect(b,zero,rawFeedback,f.configs[1].admissionPolicy).isEmpty())
   assertTrue(f.configs.single { it.index==3 }.seeds.allowsSource(b,p.inst(b,3),source))
   assertEquals(3, report.end.run)
   assertEquals(1, report.entries.size)
   assertTrue(f.processed.none { it.run % 2 == 1 && it.delta.node.location.index in listOf(6,7) })
   assertTrue(report.entries.any { it.descriptor.key.ruleId=="loop-root-sink" })
   assertTrue(f.processed.any { it.run==2 && it.delta.node.location.index==3 && f.ops.leaves(it.delta.facts).any { leaf -> leaf.fact.path.isNotEmpty() } })
  }
 }

}
