package org.opentaint.dataflow.bidi

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ExclusionSet
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Repeated DATA guidance is required until the long relay fits the field limit. */
class RepeatedDemandRelayTest {
    @Test
    fun `removing an identical second relay demand loses the later observation`() {
        checkRelay(omitRepeatedGuide = false)
        checkRelay(omitRepeatedGuide = true)
    }

    private fun checkRelay(omitRepeatedGuide: Boolean) = DriverFixtures().use { f ->
        val p = f.program
        val root = p.method("main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
        val relay = p.method("relay", listOf(listOf(1), listOf(2), listOf(3), emptyList()), 3).key()
        val localP = AccessPathBase.LocalVar(0)
        val localOut = AccessPathBase.LocalVar(1)
        val temp = AccessPathBase.LocalVar(2)
        val arg = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val chain = (1..8).map { p.field("f$it") }
        val mark = MarkSlot.Concrete(p.mark("T"))
        fun summary(vararg edges: PathEdge) = f.summary(*edges)
        val source = PathEdge(ZERO_FACT, PathFact(localP, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)
        p.entry(root, RuleStatement(summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
        p.call(root, 1, CallPlan(setOf(localP, localOut), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, summary(starEdge(localP, emptyList(), arg, emptyList()), ZERO_KEEP)),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Callees(ADDED, RETURNED, listOf(relay)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, summary(starEdge(ret, emptyList(), localOut, emptyList()), ZERO_KEEP))
        ), emptyList(), BEFORE, AFTER))
        val sink = SinkRule(f.rule("deep relay sink"), 0, listOf(p.pattern(localOut, mark = mark)), emptyList())
        p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
        // Explicit normal pass models. No overwrite/kill/alias semantics are added.
        p.statement(relay, 1, summary(keepEdge(arg), starEdge(arg, emptyList(), temp, chain)))
        p.statement(relay, 2, summary(starEdge(temp, chain, ret, emptyList())))
        val expected = DemandPattern(p.pattern(ret, tail = Tail.ANY, mark = MarkSlot.STAR),
            p.pattern(arg, tail = Tail.STAR, mark = MarkSlot.STAR))
        var repeatedHandoffs = 0
        var removedOrigins = 0
        val driver = f.driver(IncreasingLimits, budget = 20.seconds, run1MarkMode = MarkMode.FULL,
            guardBarrier = { _, body ->
                val next = body()
                if (next !is Next.Run || next.config.index !in listOf(4, 6)) next
                else {
                    val config = next.config
                    val nativeDemand = checkNotNull(config.demand)
                    assertEquals(listOf(expected), nativeDemand.explicitRows(relay))
                    repeatedHandoffs++
                    if (!omitRepeatedGuide || config.index == 4) next
                    else {
                        val demand = rebuildHandoff(f, Direction.FORWARD) { origin ->
                            val drop = origin.owner == HandoffOwner(relay) && origin.rows ==
                                listOf(PairedDemand(DemandEntry.Data(expected.entry), DemandExit.Data(checkNotNull(expected.exit))))
                            if (drop) removedOrigins++
                            drop
                        }
                        assertTrue(demand.explicitRows(relay).isEmpty())
                        Next.Run(RunConfig(config.index, config.fieldLimit, demand, config.records, config.seeds,
                            config.roots, config.disableRun1Statics, config.run1MarkMode, config.fieldLimitSchedule,
                            config.normalTargets))
                    }
                }
            })
        val report = driver.analyze(listOf(root))
        for (run in listOf(3, 5)) {
            val frontier = driver.frontiers.single { it.run == run }
            assertEquals(mapOf(root to 1, relay to 1), frontier.demandEdges)
        }
        assertEquals(2, repeatedHandoffs)
        assertEquals(if (omitRepeatedGuide) 1 else 0, removedOrigins)
        assertEquals(RunStatus.COMPLETE, report.end.status)
        assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
        assertEquals(if (omitRepeatedGuide) 7 else 9, report.end.run)
        if (omitRepeatedGuide) {
            assertTrue(report.entries.isEmpty())
        } else {
            val finding = report.entries.single()
            assertFalse(finding.provisional)
            assertEquals(sink.rule.id, finding.descriptor.key.ruleId)
            assertEquals(p.inst(root, 2), finding.descriptor.key.statement)
        }
    }
}
