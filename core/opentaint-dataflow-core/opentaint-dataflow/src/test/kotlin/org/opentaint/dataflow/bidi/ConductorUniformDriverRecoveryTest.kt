package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** E29 runs the real root/callee pipeline. No demand or saved relation is injected. */
class ConductorUniformDriverRecoveryTest {
    @Test fun `uniform source and mapper branch recover the exact sink by run5`() = DriverFixtures().use { fixture ->
        val program=fixture.program
        val root=program.method("E29 root",listOf(listOf(1),listOf(2),emptyList()),2).key()
        val mapper=program.method("E29 mapper",listOf(
            listOf(1),listOf(2,3),listOf(5),listOf(4),listOf(5),listOf(6),emptyList()),6).key()
        val x=AccessPathBase.LocalVar(0)
        val mapped=AccessPathBase.LocalVar(1)
        val p=AccessPathBase.Argument(0)
        val out=AccessPathBase.LocalVar(10)
        val part=AccessPathBase.LocalVar(11)
        val ret=AccessPathBase.Return
        val f=program.field("f")
        val g=program.field("g")
        val h=program.field("h")
        val extra=program.field("extra")
        val e=fixture.manager.accessors.index(ElementAccessor)
        val t=MarkSlot.Concrete(program.mark("T"))
        // root: sourceUniformT(x.f); mapped=mapper(x); sinkExactT(mapped.e.h).
        val source=PathEdge(ZERO_FACT,PathFact(x,listOf(f),Tail.ANY_TAINT,t),ExclusionSet.Empty)
        program.entry(root,RuleStatement(fixture.summary(ZERO_KEEP,source),StatementSummary.EMPTY,emptyList()))
        program.call(root,1,CallPlan(setOf(x,mapped),listOf(
            CallStage.Edges(BEFORE,BOUND,BIND_IN,fixture.summary(
                starEdge(x,emptyList(),p,emptyList()),ZERO_KEEP)),
            CallStage.Actions(BOUND,ADDED,emptyList()),
            CallStage.Callees(ADDED,RETURNED,listOf(mapper)),
            CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
            CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,fixture.summary(
                starEdge(ret,emptyList(),mapped,emptyList()),ZERO_KEEP)),
        ),emptyList(),BEFORE,AFTER))
        val sink=SinkRule(fixture.rule("E29 exact mapper sink"),0,
            listOf(program.pattern(mapped,listOf(e,h),Tail.EXACT,t)),emptyList())
        program.exit(root,2,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,listOf(sink)),false,emptySet()))
        // mapper: if(flag) out.e.h.extra=p; else out.e.h=p.f.g; return out.
        program.statement(mapper,2,MicroEdgeBuilder().apply {
            write(out,listOf(e,h,extra),false,listOf(p),emptyList())
        }.build())
        program.statement(mapper,3,MicroEdgeBuilder().apply { read(part,p,listOf(f,g)) }.build())
        program.statement(mapper,4,MicroEdgeBuilder().apply { write(out,listOf(e,h),false,listOf(part),emptyList()) }.build())
        program.statement(mapper,5,MicroEdgeBuilder().apply { move(ret,out) }.build())
        val report=fixture.driver(FixedLimits(listOf(1,1,2,3,4)),budget=20.seconds,
            run1MarkMode=MarkMode.FULL).analyze(listOf(root))
        assertTrue(fixture.results.all { it.status==RunStatus.COMPLETE })
        assertTrue(report.entries.any { it.descriptor.rule==sink.rule && it.descriptor.key.statement==program.inst(root,2) },
            "E29 NORMAL source-to-sink route must be recovered by run-5; runs=${fixture.configs.map { it.index }}")
        assertTrue(report.end.run<=5)
    }
}
