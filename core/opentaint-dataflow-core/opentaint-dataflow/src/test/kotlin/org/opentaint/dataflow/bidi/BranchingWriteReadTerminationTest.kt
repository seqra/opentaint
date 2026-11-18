package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Ordinary recursive field writers followed by ordinary recursive readers.
 * Every writer path ends in f. Every negative reader path ends in g.
 * Branches can add g or h at any recursive depth. */
class BranchingWriteReadTerminationTest {
    private fun run(repair: Boolean, positive: Boolean = false, observerChild: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("write then read", listOf(listOf(1),listOf(2),listOf(3),emptyList()),3).key()
            val writer = p.method("branching writer", listOf(listOf(1,2),listOf(6),listOf(3),listOf(4,5),listOf(6),listOf(6),emptyList()),6).key()
            val reader = p.method("branching reader", listOf(listOf(1,2,3),listOf(5),listOf(4),listOf(4),listOf(5),emptyList()),5).key()
            val x = AccessPathBase.LocalVar(0); val y = AccessPathBase.LocalVar(1); val z = AccessPathBase.LocalVar(2)
            val temp = AccessPathBase.LocalVar(3); val arg = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
            val fieldF = p.field("f"); val g = p.field("g"); val h = p.field("h"); val mark = MarkSlot.Concrete(p.mark("T"))
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP,PathEdge(ZERO_FACT,PathFact(x,emptyList(),Tail.EXACT,mark),ExclusionSet.Empty)),StatementSummary.EMPTY,emptyList()))
            fun call(input: AccessPathBase, output: AccessPathBase, callee: MethodKey) = CallPlan(setOf(input),listOf(
                CallStage.Edges(BEFORE,BOUND,BIND_IN,f.summary(ZERO_KEEP,starEdge(input,emptyList(),arg,emptyList()))),
                CallStage.Actions(BOUND,ADDED,emptyList()), CallStage.Callees(ADDED,RETURNED,listOf(callee)),
                CallStage.Actions(RETURNED,REWRITTEN,emptyList()),
                CallStage.Edges(REWRITTEN,AFTER,BIND_BACK,f.summary(ZERO_KEEP,starEdge(ret,emptyList(),output,emptyList())))
            ),emptyList(),BEFORE,AFTER)
            p.call(main,1,call(x,y,writer)); p.call(main,2,call(y,z,reader))
            p.statement(writer,1,f.summary(ZERO_KEEP,starEdge(arg,emptyList(),ret,listOf(fieldF))))
            p.call(writer,2,call(arg,temp,writer))
            p.statement(writer,4,f.summary(ZERO_KEEP,starEdge(temp,emptyList(),ret,listOf(g))))
            p.statement(writer,5,f.summary(ZERO_KEEP,starEdge(temp,emptyList(),ret,listOf(h))))
            p.statement(reader,1,f.summary(ZERO_KEEP,starEdge(arg,listOf(if (positive) fieldF else g),ret,emptyList())))
            p.statement(reader,2,f.summary(ZERO_KEEP,starEdge(arg,listOf(g),temp,emptyList())))
            p.statement(reader,3,f.summary(ZERO_KEEP,starEdge(arg,listOf(h),temp,emptyList())))
            p.call(reader,4,call(temp,ret,reader))
            p.exit(main,3,ExitRules(RuleStatement(StatementSummary.EMPTY,StatementSummary.EMPTY,listOf(
                SinkRule(f.rule("exact observer"),0,listOf(p.pattern(z,if (observerChild) listOf(fieldF) else emptyList(),tail=Tail.EXACT,mark=mark)),emptyList()))),false,emptySet()))
            var rewrites = 0
            val driver = f.driver(if (repair) IncreasingLimits else TerminationBaselinePolicy,30.seconds,
                run1MarkMode=MarkMode.FULL, invokeRun = { config, owner, timeout ->
                    val previous = f.configs.lastOrNull()
                    // Both finite grammars cover every ordinary branch above.
                    // Source is exactly x.$/T; observer is exactly z.$/T.
                    // The proof query is available after run1's joined seal.
                    val wGrammar = RegularFieldPathQuery.grammar(listOf(fieldF),listOf(listOf(g),listOf(h)))
                    val rGrammar = RegularFieldPathQuery.grammar(listOf(if (positive) fieldF else g) + (if (observerChild) listOf(fieldF) else emptyList()),listOf(listOf(g),listOf(h)))
                    val impossible = RegularFieldPathQuery.disjoint(wGrammar,rGrammar) == true
                    val previouslyServed = previous?.normalTargets?.zeroRows()?.any { it.method == main } == true
                    val eligible = repair && config.direction == Direction.BACKWARD && previous != null && !previous.run1 &&
                        (impossible || previouslyServed)
                    val actual = if (eligible) {
                        rewrites++
                        RunConfig(config.index,config.fieldLimit,withoutCertifiedRootTarget(f,previous!!,main),config.records,config.seeds,config.roots,
                            run1MarkMode=config.run1MarkMode,fieldLimitSchedule=config.fieldLimitSchedule,
                            normalTargets=config.normalTargets)
                    } else config
                    f.run(actual,owner,timeout)
                })
            val report = driver.analyze(listOf(main))
            println("BRANCHING_WR end=${report.end} normal=${report.entries.count { !it.provisional }}")
            if (!repair && report.end.status in setOf(RunStatus.TIMEOUT, RunStatus.OOM)) {
                val completed = driver.frontiers.last()
                println("TERMINATION_BASELINE lastCompleted=${completed.run} targets=${completed.targetDemand}")
                assertTrue(driver.frontiers.any { it.run >= 9 && it.run % 2 == 1 && it.targetDemand > 0 })
                return
            }
            for (run in f.results.filter { it.status == RunStatus.COMPLETE }) {
                val root = run.analyzers.singleOrNull { it.key==main }
                println("BRANCHING_WR run=${run.runIndex} targets=${root?.outgoingTargets} rows=${run.analyzers.map { it.key to it.summaries.all().count() }}")
            }
            assertEquals(RunStatus.COMPLETE,report.end.status)
            assertEquals(if (repair) EndReason.NO_DEMAND_EDGE else EndReason.RUN_LIMIT,report.end.reason)
            if (!repair) {
                assertEquals(TERMINATION_BASELINE_LAST_RUN,report.end.run)
                assertTrue(f.results.filter { it.runIndex%2==1 }.all { run ->
                    run.analyzers.single { it.key==main }.outgoingTargets.isNotEmpty()
                })
            } else assertTrue(rewrites>0)
            assertEquals(if (positive || observerChild) 1 else 0,report.entries.count { !it.provisional })
        }
    }
    @Test fun `disjoint recursive write and read paths keep root demand through diagnostic run101`() = run(false)
    @Test fun `regular no-route certificate retires only the impossible root Target`() = run(true)
    @Test fun `overlapping recursive paths keep their real NORMAL observation`() = run(true,positive=true)
    @Test fun `a different exact observer position cannot borrow root no-route service`() = run(true,observerChild=true)
}
