package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Fully analyzed recursion with a returning base case. Each recursive
 * branch puts its result in one field of a fresh wrapper. No CFG loop,
 * cleaner, unresolved body, pass rule or supplied method summary. */
class RecursiveWrapperTerminationTest {
    private fun run(repair: Boolean, mutual: Boolean = false, negative: Boolean = false, twoOrigins: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("recursive wrapper main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val wrap = p.method("wrap", listOf(listOf(1,2), listOf(5), listOf(3), listOf(4), listOf(5), emptyList()), 5).key()
            val other = if (mutual) p.method("other wrapper", listOf(listOf(1,2), listOf(5), listOf(3), listOf(4), listOf(5), emptyList()), 5).key() else null
            val x = AccessPathBase.LocalVar(0); val result = AccessPathBase.LocalVar(1)
            val temp = AccessPathBase.LocalVar(2); val box = AccessPathBase.LocalVar(3)
            val arg = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
            val field = p.field("f"); val leaf = p.field("g"); val t = p.mark("T")
            val sources = listOf(PathEdge(ZERO_FACT,
                PathFact(x, listOf(field,leaf), Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty)) +
                if (twoOrigins) listOf(PathEdge(ZERO_FACT,
                    PathFact(x, List(4) { field }, Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty)) else emptyList()
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP, *sources.toTypedArray()),
                StatementSummary.EMPTY, emptyList()))
            fun call(from: AccessPathBase, to: AccessPathBase, callee: MethodKey = wrap) = CallPlan(setOf(from), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(from, emptyList(), arg, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(ret, emptyList(), to, emptyList())))
            ), emptyList(), BEFORE, AFTER)
            p.call(main, 1, call(x, result))
            p.statement(wrap, 1, f.summary(ZERO_KEEP, starEdge(arg, emptyList(), ret, emptyList())))
            p.call(wrap, 2, call(arg, temp, other ?: wrap))
            p.statement(wrap, 3, f.summary(ZERO_KEEP, starEdge(temp, emptyList(), box, listOf(field))))
            p.statement(wrap, 4, f.summary(ZERO_KEEP, starEdge(box, emptyList(), ret, emptyList())))
            if (other != null) {
                p.statement(other, 1, f.summary(ZERO_KEEP, starEdge(arg, emptyList(), ret, emptyList())))
                p.call(other, 2, call(arg, temp))
                p.statement(other, 3, f.summary(ZERO_KEEP, starEdge(temp, emptyList(), box, listOf(field))))
                p.statement(other, 4, f.summary(ZERO_KEEP, starEdge(box, emptyList(), ret, emptyList())))
            }
            val sink = SinkRule(f.rule("observe recursive return"), 0,
                listOf(p.pattern(result, if (negative) listOf(leaf) else emptyList(), tail = Tail.ANY,
                    mark = MarkSlot.Concrete(t))), emptyList())
            p.exit(main, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            var adaptedTransitions = 0
            val report = f.driver(if (repair || negative) IncreasingLimits else TerminationBaselinePolicy, 30.seconds,
                run1MarkMode = MarkMode.FULL, invokeRun = { config, owner, timeout ->
                    // Single-origin fixture adapter only. The general proposal
                    // uses the proved one-bit terminal provenance fixed point.
                    // DATA handoff rows and saved records remain present.
                    val previous = f.configs.lastOrNull()
                    val normalBefore = f.processed.filter { row -> row.run < config.index - 1 && row.run % 2 == 1 &&
                        row.method == main && row.delta.node == p.inst(main, 2) && row.delta.facts.layer == Layer.NORMAL
                    }.flatMap { row -> f.ops.leaves(row.delta.facts).toList() }
                    // R38 fixture certificate: all full-mark generators are
                    // explicit above, and pure FLOW wrappers preserve each
                    // source suffix. No source labels are put on DATA facts.
                    val bothOriginsServed = normalBefore.any { it.fact.base == result && it.fact.tail == Tail.EXACT && it.fact.path.lastOrNull() == leaf } &&
                        normalBefore.any { it.fact.base == result && it.fact.tail == Tail.EXACT && it.fact.path.size >= 4 && it.fact.path.all { it == field } }
                    val confirmedBeforeForward = if (twoOrigins) bothOriginsServed
                        else previous?.normalTargets?.zeroRows()?.any { it.method == main } == true
                    val actual = if (repair && config.direction == Direction.BACKWARD && confirmedBeforeForward) {
                        adaptedTransitions++
                        val last = f.results.last()
                        val builder = DemandStore.Builder(f.manager)
                        for (actor in last.analyzers) {
                            for ((premise,facts) in actor.summaries.demandEdges(previous!!.direction))
                                for (row in projectSummaryGuidance(f.manager,premise,facts)) builder.add(actor.key,row)
                            for (target in actor.outgoingTargets) {
                                if (actor.key == main && target.premise.isZero) continue
                                for (row in projectTargetGuidance(target)) builder.add(actor.key,row)
                            }
                        }
                        RunConfig(config.index,config.fieldLimit,builder.build(),config.records,config.seeds,
                            config.roots,run1MarkMode=config.run1MarkMode,fieldLimitSchedule=config.fieldLimitSchedule,
                            normalTargets=config.normalTargets)
                    } else config
                    f.run(actual,owner,timeout)
                }).analyze(listOf(main))
            println("RECURSIVE_WRAPPER end=${report.end} findings=${report.entries.size}")
            for (run in f.results) {
                val root = run.analyzers.singleOrNull { it.key == main }
                val callee = run.analyzers.singleOrNull { it.key == wrap }
                val rows = callee?.summaries?.all()?.flatMap { (premise,facts) ->
                    f.ops.leaves(facts).filter { it.fact.base == ret }.map { leaf ->
                        "${premise.members.map { it.toPattern() }} -> $leaf ${facts.layer}"
                    }.toList()
                }?.toList()
                println("RECURSIVE_WRAPPER run=${run.runIndex} rootTargets=${root?.outgoingTargets} rootNormal=${root?.targets?.count { it.target is Target.NormalTarget }} rows=$rows")
            }
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(if (negative) 0 else 1, report.entries.count { !it.provisional })
            if (negative) {
                assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
                assertEquals(3,report.end.run)
            } else if (mutual) {
                assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
                assertEquals(5,report.end.run)
                assertEquals(0,adaptedTransitions)
            } else if (repair) {
                assertEquals(EndReason.NO_DEMAND_EDGE,report.end.reason)
                assertEquals(if (twoOrigins) 9 else 7,report.end.run)
                assertEquals(1,adaptedTransitions)
            } else {
                assertEquals(EndReason.RUN_LIMIT,report.end.reason)
                assertEquals(TERMINATION_BASELINE_LAST_RUN,report.end.run)
                assertTrue(f.results.all { result -> result.analyzers.single { it.key == main }.outgoingTargets.isNotEmpty() })
            }
        }
    }
    @Test fun `recursive field wrappers repeat root demand through diagnostic run101`() = run(false)
    @Test fun `covered root terminal handoff stops at run7 and retains the normal observation`() = run(true)
    @Test fun `mutual recursion preserves its earlier natural run5 completion`() = run(true,mutual=true)
    @Test fun `mutual recursion already completes naturally without the adapter`() = run(false,mutual=true)
    @Test fun `an unreachable sibling observation remains absent without a coverage certificate`() = run(true,negative=true)
    @Test fun `two recursive marking origins still repeat without the adapter`() = run(false,twoOrigins=true)
    @Test fun `both recursive marking origins are served before natural run9`() = run(true,twoOrigins=true)
}
