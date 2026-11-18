package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Two actual loop decompositions: wrap in g/h, then read g/h, then g.
 * There is no source/observer inside a loop and no special transfer rule. */
class LoopWriteReadTerminationTest {
    private fun run(repair: Boolean, positive: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("loop writes then loop reads",listOf(listOf(1),listOf(2),listOf(3,5,7),
                listOf(4),listOf(2),listOf(6),listOf(2),listOf(8,9,10),listOf(7),listOf(7),listOf(11),emptyList()),11).key()
            val x = AccessPathBase.LocalVar(0); val y = AccessPathBase.LocalVar(1)
            val z = AccessPathBase.LocalVar(2); val tmp = AccessPathBase.LocalVar(3)
            val fieldF = p.field("f"); val g = p.field("g"); val h = p.field("h"); val mark = MarkSlot.Concrete(p.mark("T"))
            p.entry(main,RuleStatement(f.summary(ZERO_KEEP,PathEdge(ZERO_FACT,PathFact(x,emptyList(),Tail.EXACT,mark),ExclusionSet.Empty)),StatementSummary.EMPTY,emptyList()))
            fun assign(from: AccessPathBase, read: List<Int>, to: AccessPathBase, write: List<Int>, keep: Boolean) =
                StatementSummary(setOf(AccessPathBase.Zero,from,to),listOf(MicroEdge.of(ZERO_KEEP)) +
                    (if (keep && from != to) listOf(MicroEdge.of(keepEdge(from))) else emptyList()) +
                    listOf(MicroEdge.of(starEdge(from,read,to,write))),emptyList(),emptyMap())
            p.statement(main,1,assign(x,emptyList(),y,listOf(fieldF),true))
            p.statement(main,3,assign(y,emptyList(),tmp,listOf(g),true))
            p.statement(main,4,assign(tmp,emptyList(),y,emptyList(),true))
            p.statement(main,5,assign(y,emptyList(),tmp,listOf(h),true))
            p.statement(main,6,assign(tmp,emptyList(),y,emptyList(),true))
            p.statement(main,8,assign(y,listOf(g),y,emptyList(),false))
            p.statement(main,9,assign(y,listOf(h),y,emptyList(),false))
            p.statement(main,10,assign(y,listOf(if (positive) fieldF else g),z,emptyList(),true))
            p.exit(main,11,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,listOf(
                SinkRule(f.rule("exact loop observer"),0,listOf(p.pattern(z,tail=Tail.EXACT,mark=mark)),emptyList()))),false,emptySet()))
            val w = RegularFieldPathQuery.grammar(listOf(fieldF),listOf(listOf(g),listOf(h)))
            val r = RegularFieldPathQuery.grammar(listOf(if (positive) fieldF else g),listOf(listOf(g),listOf(h)))
            val noRoute = RegularFieldPathQuery.disjoint(w,r) == true
            var rewrites = 0
            val report = f.driver(if (repair) IncreasingLimits else TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL,invokeRun = { config, owner, timeout ->
                    val previous = f.configs.lastOrNull()
                    val normalBefore = previous?.normalTargets?.zeroRows()?.any { it.method==main } == true
                    val actual = if (repair && config.direction==Direction.BACKWARD && previous!=null && !previous.run1 && (noRoute || normalBefore)) {
                        rewrites++
                        RunConfig(config.index,config.fieldLimit,withoutCertifiedRootTarget(f,previous,main),config.records,config.seeds,config.roots,
                            run1MarkMode=config.run1MarkMode,fieldLimitSchedule=config.fieldLimitSchedule,normalTargets=config.normalTargets)
                    } else config
                    f.run(actual,owner,timeout)
                }).analyze(listOf(main))
            println("LOOP_WR repair=$repair positive=$positive end=${report.end} findings=${report.entries.count { !it.provisional }} rewrites=$rewrites")
            for (result in f.results) println("LOOP_WR run=${result.runIndex} targets=${result.analyzers.singleOrNull { it.key==main }?.outgoingTargets}")
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertEquals(if (positive) 1 else 0,report.entries.count { !it.provisional })
            if (repair) assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
            else { assertEquals(5,report.end.run); assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason) }
        }
    }
    @Test fun `ordinary loop restriction already closes the disjoint two-loop control at run5`() = run(false)
    @Test fun `complete regular certificate preserves all block DATA ports`() = run(true)
    @Test fun `overlapping loop languages retain their real observation`() = run(true,positive=true)
}
