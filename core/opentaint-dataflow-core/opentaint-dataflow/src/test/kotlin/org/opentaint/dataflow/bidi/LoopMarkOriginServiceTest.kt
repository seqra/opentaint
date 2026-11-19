package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Counterexample to using a report ID as proof that both loop origins are served. */
class LoopMarkOriginServiceTest {
    private fun run(retireByReportId: Boolean, nested: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            val exit = if (nested) 7 else 5
            val graph = if (nested) listOf(listOf(1,2), listOf(3), listOf(3), listOf(4,7),
                listOf(5,6), listOf(4), listOf(3), emptyList())
                else listOf(listOf(1,2), listOf(3), listOf(3), listOf(4,5), listOf(3), emptyList())
            val main = p.method("loop with two marking origins", graph, exit).key()
            val r = AccessPathBase.LocalVar(0); val field = p.field("f"); val g = p.field("g")
            val mark = MarkSlot.Concrete(p.mark("T"))
            fun gen(fields: List<Int>) = f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT, PathFact(r, fields, Tail.EXACT, mark), ExclusionSet.Empty))
            p.statement(main, 1, gen(listOf(g)))
            p.statement(main, 2, gen(List(4) { field }))
            p.statement(main, if (nested) 5 else 4, f.summary(ZERO_KEEP, starEdge(r, listOf(field), r, emptyList())))
            p.exit(main, exit, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(SinkRule(f.rule("loop observer"), 0,
                    listOf(p.pattern(r, tail = Tail.ANY, mark = mark)), emptyList()))), false, emptySet()))
            fun deepBefore(run: Int) = f.processed.any { row ->
                row.run < run && row.run % 2 == 1 && row.method == main && row.delta.node == p.inst(main, exit) &&
                    row.delta.facts.layer == Layer.NORMAL && f.ops.leaves(row.delta.facts).any {
                        it.fact.base == r && it.fact.path == List(4) { field } && it.fact.tail == Tail.EXACT && it.fact.mark == mark
                    }
            }
            var retired = false
            val report = f.driver(IncreasingLimits, 30.seconds, run1MarkMode = MarkMode.FULL,
                guardBarrier = { _, body ->
                    val next = body()
                    val run = f.results.last().runIndex
                    val known = f.configs.last().normalTargets.zeroRows().any()
                    if (retireByReportId && run % 2 == 1 && known) {
                        val actor = f.results.last().analyzers.single { it.key == main }
                        assertTrue(actor.summaries.demandEdges(Direction.FORWARD).none())
                        assertTrue(actor.outgoingTargets.all { it.premise.isZero })
                        retired = true
                        Next.End(RunStatus.COMPLETE, EndReason.NO_DEMAND_EDGE)
                    } else next
                }).analyze(listOf(main))
            assertEquals(retireByReportId, retired)
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            // Hierarchical block C2/C5 causes more refinement steps than
            // the flat branch control. This is natural completion, not an
            // iteration cutoff or a changed field-limit schedule.
            assertEquals(if (retireByReportId) 5 else if (nested) 17 else 13, report.end.run)
            assertEquals(!retireByReportId, deepBefore(report.end.run+1))
            assertEquals(1, report.entries.count { !it.provisional })
        }
    }
    @Test fun `native loop baseline retains the deep marking route at run13`() = run(false)
    @Test fun `report-only retirement also loses the loop route at run5`() = run(true)
    @Test fun `native nested loop baseline retains both marking origins`() = run(false, nested = true)
    @Test fun `report-only retirement loses the nested loop marking route`() = run(true, nested = true)
}
