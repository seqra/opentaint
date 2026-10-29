package org.opentaint.dataflow.bidi

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

/** A small version of the OWASP getBytes/Base64/String model cycle.
 *
 * Code under analysis:
 *     main() { sink(helper(sourceAll())); }
 *     helper(p) { bytes = getBytes(p); return newString(bytes); }
 *
 * getBytes has p.* -> bytes.* and p.H.* -> bytes.*. The constructor has
 * bytes.* -> out.* and bytes.* -> out.H.*. H is a named model storage field.
 * Every supplied micro-edge has STAR tails. The AP operations, not this
 * fixture, create ANY/DEMAND when a root leaf is above the field read.
 *
 * Forward: p.* / FLOW N -> bytes.[any] / FLOW D -> ret.[any] / FLOW D.
 * Backward: ret.* / FLOW N -> bytes.[any] / FLOW D -> p.[any] / FLOW D.
 * The next local demand can therefore admit p.* / FLOW again. The test uses
 * the real driver, engines, handoffs, records, restriction and reversal.
 */
class OwaspDemandCycleTest {
    private val argument = AccessPathBase.Argument(0)
    private val returned = AccessPathBase.Return

    private data class Case(val root: MethodKey, val helper: MethodKey, val field: Int)
    private data class Selected(val method: MethodKey, val premise: Set<Pattern>, val result: Conclusion)

    private fun straight(size: Int) = List(size) { if (it + 1 < size) listOf(it + 1) else emptyList() }

    private fun build(f: DriverFixtures, withStorageRoutes: Boolean): Case {
        val p = f.program
        val root = p.method("OWASP model caller", straight(3), 2).key()
        val helper = p.method("OWASP model helper", straight(5), 4).key()
        val input = AccessPathBase.LocalVar(0)
        val result = AccessPathBase.LocalVar(1)
        val bytes = AccessPathBase.LocalVar(2)
        val out = AccessPathBase.LocalVar(3)
        val field = p.field("<string-bytes>")
        val mark = MarkSlot.Concrete(p.mark("T"))
        val source = PathEdge(ZERO_FACT, PathFact(input, emptyList(), Tail.ANY_TAINT, mark), ExclusionSet.Empty)
        p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
        p.call(root, 1, CallPlan(setOf(input, result), listOf(
            CallStage.Edges(BEFORE, AFTER, PASS_OVER, f.summary(keepEdge(input))),
            CallStage.Edges(BEFORE, BOUND, BIND_IN,
                f.summary(ZERO_KEEP, starEdge(input, emptyList(), argument, emptyList()))),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Callees(ADDED, RETURNED, listOf(helper)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK,
                f.summary(ZERO_KEEP, starEdge(returned, emptyList(), result, emptyList()))),
        ), emptyList(), BEFORE, AFTER))
        val sink = SinkRule(f.rule("OWASP model sink"), 0,
            listOf(p.pattern(result, tail = Tail.ANY, mark = mark)), emptyList())
        p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(sink)), false, emptySet()))

        p.statement(helper, 1, MicroEdgeBuilder().apply {
            move(bytes, argument)
            if (withStorageRoutes) edge(starEdge(argument, listOf(field), bytes, emptyList()))
        }.build())
        p.statement(helper, 2, MicroEdgeBuilder().apply {
            move(out, bytes)
            if (withStorageRoutes) edge(starEdge(bytes, emptyList(), out, listOf(field)))
        }.build())
        p.statement(helper, 3, MicroEdgeBuilder().apply { move(returned, out) }.build())
        return Case(root, helper, field)
    }

    private fun selected(f: DriverFixtures, result: RunResult<RunMethodAnalyzer>): Set<Selected> =
        result.analyzers.flatMap { actor -> actor.summaries.demandEdges().flatMap { (premise, facts) ->
            f.ops.leaves(facts).map { Selected(actor.key, premise.members.map { it.toPattern() }.toSet(),
                Conclusion(it.fact, it.exclusion, facts.layer == Layer.DEMAND)) }
        } }.toSet()

    @Test
    fun `named storage routes repeat FLOW demand while each engine completes`(): Unit {
        DriverFixtures().use { f ->
            val case = build(f, withStorageRoutes = true)
            val productionDecisions = ArrayList<Int>()
            val cappedPolicy = object : IterationPolicy by IncreasingLimits {
                override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>,
                                           frontiers: List<Frontier>): Boolean {
                    assertTrue(IncreasingLimits.continueAfter(run, result, frontiers))
                    productionDecisions += run.index
                    return run.index < 9
                }
            }
            val driver = f.driver(cappedPolicy, budget = 15.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(case.root))

            assertEquals((1..9).toList(), f.configs.map { it.index })
            assertEquals(listOf(1, 1, 2, 3, 4, 5, 6, 7, 8), f.configs.map { it.fieldLimit })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals(listOf(1, 3, 5, 7, 9), productionDecisions,
                "Both production stop checks allow every complete forward run to reach the policy")
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 9, Direction.FORWARD, EndReason.POLICY), report.end)
            assertEquals(ReportState.DEMAND, report.entries.single().state)
            assertEquals(9, report.entries.single().run)

            val expectedPremise = setOf(f.program.pattern(argument, tail = Tail.STAR, mark = MarkSlot.STAR))
            val expected = setOf(Selected(case.helper, expectedPremise,
                Conclusion(PathFact(returned, emptyList(), Tail.ANY, MarkSlot.STAR), ExclusionSet.Empty, true)))
            for (run in listOf(5, 7, 9)) {
                val result = f.results[run - 1]
                assertEquals(expected, selected(f, result), "Exact selected relation set in run-$run")
                assertTrue(result.demandLayerEdges > 0L, "Fresh DEMAND work remains in run-$run")
                assertEquals(1, driver.frontiers[run - 1].demandVulnerabilities)
                assertTrue(f.processed.any { it.run == run && it.method == case.helper &&
                    it.delta.facts is FlowTree && it.delta.facts.layer == Layer.DEMAND &&
                    f.ops.leaves(it.delta.facts).any { leaf -> leaf.fact.tail == Tail.ANY } },
                    "The count is backed by processed FLOW/ANY DEMAND points")
            }
            val nextSix = f.configs[5].demand!!.explicitRows(case.helper).toSet()
            val nextEight = f.configs[7].demand!!.explicitRows(case.helper).toSet()
            assertEquals(nextSix, nextEight, "The actual run-5 and run-7 handoffs are equal")
            assertEquals(expected.mapTo(LinkedHashSet()) { DemandPattern(
                Pattern(it.result.fact, it.result.exclusion), it.premise.single()) }, nextSix)
            for (run in listOf(5, 7, 9)) {
                assertTrue(f.configs[run - 1].demand!!.explicitRows(case.helper).any { row ->
                    row.entry.fact.base == argument && row.entry.fact.path.isEmpty() &&
                        row.entry.fact.mark is MarkSlot.Star
                }, "Actual backward handoff keeps admitting a root abstract initial in run-$run")
            }
            assertTrue(f.program.statementInputs.filter { it.key == case.helper }.flatMap { it.summary.edges }
                .all { it.edge.from.tail == Tail.STAR && it.edge.to.tail == Tail.STAR &&
                    it.edge.from.path.size <= 1 && it.edge.to.path.size <= 1 },
                "No supplied may target or long field path creates the repeated demand")
            val backwardEntry = f.program.pattern(returned, tail = Tail.STAR, mark = MarkSlot.STAR)
            assertTrue(f.records.byEntry(case.helper, backwardEntry).any { record ->
                record.direction == Direction.BACKWARD && record.premise.toPattern() == backwardEntry &&
                    record.conclusion.layer == Layer.NORMAL &&
                    f.ops.leaves(record.conclusion).any { leaf ->
                        leaf == f.program.pattern(argument, listOf(case.field), tail = Tail.STAR,
                            mark = MarkSlot.STAR)
                    }
            }, "A precise NORMAL backward record can coexist with the recurring coarse demand")
        }
    }

    @Test
    fun `root copy control stops without the named storage routes`(): Unit {
        DriverFixtures().use { f ->
            val case = build(f, withStorageRoutes = false)
            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4, 5, 6, 7, 8)),
                budget = 15.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(case.root))
            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(0L, f.results.last().demandLayerEdges)
            assertTrue(selected(f, f.results.last()).isEmpty())
            assertEquals(ReportState.DEMAND, report.entries.single().state,
                "A candidate alone does not force another run after the work becomes normal")
        }
    }
}
