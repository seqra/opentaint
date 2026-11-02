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

class LoopBlockNoLeaveTest {
 @Test fun `scoped FULL no leave loop keeps exceptional discovery and completes run three`() {
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
   val demand2=f.configs.single { it.index==2 }.demand!!
   val rawFeedback=p.fact(x,listOf(fld),Tail.EXACT,t)
   val zero=f.manager.zero
   assertTrue(demand2.intersect(b,zero,rawFeedback,f.configs[1].admissionPolicy).isEmpty())
   assertTrue(f.configs.single { it.index==3 }.seeds.allowsSource(b,p.inst(b,3),source))
   assertTrue(f.results.any { run -> run.analyzers.any { it.blockTargets().any() } },
    "This control must execute the method-owned block path")
   assertEquals(3, report.end.run)
   assertEquals(1, report.entries.size)
   assertTrue(f.processed.none { it.run % 2 == 1 && it.delta.node.location.index in listOf(6,7) })
   assertTrue(report.entries.any { it.descriptor.key.ruleId=="loop-root-sink" })
   assertTrue(f.processed.any { it.run==2 && it.delta.node.location.index==3 && f.ops.leaves(it.delta.facts).any { leaf -> leaf.fact.path.isNotEmpty() } })
  }
 }

}
