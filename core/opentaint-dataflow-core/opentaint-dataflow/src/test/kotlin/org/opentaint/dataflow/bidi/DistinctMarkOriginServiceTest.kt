package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** A report ID can be known before both marking paths reach the observer. */
class DistinctMarkOriginServiceTest {
    private fun run(retireByReportId: Boolean, growAfterMarking: Boolean = false) {
        DriverFixtures().use { f ->
            val p = f.program
            val exit = if (growAfterMarking) 10 else 6
            val graph = (0..exit).map { node -> when (node) {
                0 -> listOf(1,2); 1 -> listOf(exit); exit -> emptyList(); else -> listOf(node+1)
            } }
            val main = p.method("two marking points", graph, exit).key()
            val x = AccessPathBase.LocalVar(0); val a = AccessPathBase.LocalVar(1)
            val b = AccessPathBase.LocalVar(2); val r = AccessPathBase.LocalVar(3)
            val field = p.field("f"); val g = p.field("g"); val t = p.mark("T")
            val mark = MarkSlot.Concrete(t)
            fun marking(base: AccessPathBase, fields: List<Int>) = f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT, PathFact(base, fields, Tail.EXACT, mark), ExclusionSet.Empty))
            p.statement(main, 1, marking(r, listOf(g)))
            p.statement(main, 2, marking(x, if (growAfterMarking) emptyList() else List(4) { field }))
            fun move(input: AccessPathBase, read: List<Int>, output: AccessPathBase, write: List<Int>) = StatementSummary(
                setOf(AccessPathBase.Zero, input, output), listOf(MicroEdge.of(ZERO_KEEP),
                    MicroEdge.of(keepEdge(input)), MicroEdge.of(starEdge(input, read, output, write))),
                emptyList(), emptyMap())
            var from: AccessPathBase = x
            if (growAfterMarking) for (i in 0..3) {
                val next = AccessPathBase.LocalVar(4+i)
                p.statement(main, 3+i, move(from, emptyList(), next, listOf(field)))
                from = next
            }
            p.statement(main, exit-3, move(from, listOf(field), a, emptyList()))
            p.statement(main, exit-2, move(a, listOf(field), b, emptyList()))
            p.statement(main, exit-1, move(b, listOf(field), r, emptyList()))
            val observer = SinkRule(f.rule("one observer"), 0,
                listOf(p.pattern(r, tail = Tail.ANY, mark = mark)), emptyList())
            p.exit(main, exit, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(observer)), false, emptySet()))
            var omitted = false
            val report = f.driver(IncreasingLimits, 30.seconds, run1MarkMode = MarkMode.FULL,
                guardBarrier = { _, body ->
                    val next = body()
                    val last = f.results.lastOrNull()
                    val previous = f.configs.lastOrNull()
                    if (retireByReportId && last?.runIndex?.rem(2) == 1 &&
                        previous?.normalTargets?.zeroRows()?.any() == true) {
                        val actor = last.analyzers.single { it.key == main }
                        assertTrue(actor.summaries.demandEdges(Direction.FORWARD).none())
                        assertTrue(actor.outgoingTargets.all { it.premise.isZero })
                        omitted = true
                        Next.End(RunStatus.COMPLETE, EndReason.NO_DEMAND_EDGE)
                    } else next
                }).analyze(listOf(main))
            fun hasDeep(run: Int) = f.processed.any { processed ->
                processed.run == run && processed.method == main && processed.delta.node == p.inst(main, exit) &&
                    processed.delta.facts.layer == Layer.NORMAL && f.ops.leaves(processed.delta.facts).any {
                        it.fact.base == r && it.fact.path == listOf(field) && it.fact.tail == Tail.EXACT && it.fact.mark == mark
                    }
            }
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(1, report.entries.count { !it.provisional })
            assertFalse(hasDeep(1)); assertFalse(hasDeep(3))
            if (retireByReportId) {
                assertTrue(omitted); assertEquals(3, report.end.run)
                assertTrue(f.results.none { hasDeep(it.runIndex) })
            } else {
                assertEquals(5, report.end.run); assertTrue(hasDeep(5))
            }
        }
    }
    @Test fun `native baseline refines the second marking route at run5`() = run(false)
    @Test fun `report identity alone retires the second route too early at run3`() = run(true)
    @Test fun `NORMAL marking activation does not cover a later truncated path`() = run(true, growAfterMarking = true)
    @Test fun `baseline later path after a NORMAL activation finishes at run5`() = run(false, growAfterMarking = true)
}
