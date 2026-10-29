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
 * Run 1 creates a coarse ANY/FLOW demand. Restricted admission must refine
 * that demand with the actual uniform source instead of reopening p.*.
 * The test uses the real driver, engines, handoffs, records, restriction
 * and reversal. It must stop without a policy cap and retain the sink.
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
    fun `named storage routes refine once and retain the sink without a policy cap`(): Unit {
        DriverFixtures().use { f ->
            val case = build(f, withStorageRoutes = true)
            val driver = f.driver(IncreasingLimits, budget = 15.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(case.root))

            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertEquals(listOf(1, 1, 2), f.configs.map { it.fieldLimit })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD,
                EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(0L, f.results.last().demandLayerEdges)
            assertTrue(selected(f, f.results.last()).isEmpty())
            assertEquals(ReportState.DEMAND, report.entries.single().state)
            assertEquals(3, report.entries.single().run)
            assertEquals("OWASP model sink", report.entries.single().key.rule.id)
            assertTrue(report.entries.single().witnesses.isNotEmpty(),
                "The real source-to-sink path survives demand refinement")

            val runOne = f.results.first()
            assertTrue(selected(f, runOne).any { row ->
                row.method == case.helper && row.result.fact.base == returned &&
                    row.result.fact.tail == Tail.ANY && row.result.fact.mark is MarkSlot.Star
            }, "The reproducer still creates the original coarse FLOW demand in run-1")
            val runThreeInitials = f.processed.filter { it.run == 3 && it.method == case.helper }
                .flatMap { it.delta.premise.members }
            assertTrue(runThreeInitials.none { initial ->
                initial.isFlow && initial.tail == Tail.STAR && initial.pathArray.isEmpty()
            }, "An ANY demand must not reopen the already handled root STAR/FLOW query")
            assertTrue(f.program.statementInputs.filter { it.key == case.helper }.flatMap { it.summary.edges }
                .all { it.edge.from.tail == Tail.STAR && it.edge.to.tail == Tail.STAR &&
                    it.edge.from.path.size <= 1 && it.edge.to.path.size <= 1 },
                "The supplied model still has no may target or long field path")
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

    /**
     * Source: assign exact T to q.g. Sink: check exact T at r.g.
     *
     * main() { source(q.g); r = m(q); sink(r.g); }
     * m(p) { p.f = new Leaf(); return p; } // f != g
     *
     * Run 1: p.* / FLOW -> ret.* / FLOW, DEMAND, no NORMAL return cover.
     * Run 2: ret.g.$ / T must admit ret.* / FLOW and retain E={f} on p.*.
     * Run 3: the NORMAL reverse record preserves the actual g suffix.
     */
    @Test
    fun `requested run2 STAR keeps the source path through a sibling overwrite`(): Unit {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("sibling overwrite caller", straight(3), 2).key()
            val helper = p.method("sibling overwrite helper", straight(4), 3).key()
            val input = AccessPathBase.LocalVar(0)
            val result = AccessPathBase.LocalVar(1)
            val written = p.field("f")
            val retained = p.field("g")
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT,
                PathFact(input, listOf(retained), Tail.EXACT, mark), ExclusionSet.Empty)
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
            p.statement(helper, 1, MicroEdgeBuilder().apply {
                write(argument, listOf(written), weak = false, values = emptyList(), aliasPaths = emptyList())
            }.build())
            p.statement(helper, 2, MicroEdgeBuilder().apply { move(returned, argument) }.build())
            val sink = SinkRule(f.rule("sibling overwrite sink"), 0,
                listOf(p.pattern(result, listOf(retained), mark = mark)), emptyList())
            p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(sink)), false, emptySet()))

            val driver = f.driver(IncreasingLimits, budget = 15.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD,
                EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals("sibling overwrite sink", report.entries.single().key.rule.id)
            assertEquals(3, report.entries.single().run)
            assertTrue(report.entries.single().witnesses.isNotEmpty())

            val runOne = f.results.first().analyzers.single { it.key == helper }
            val flowInput = p.pattern(argument, tail = Tail.STAR, mark = MarkSlot.STAR)
            val flowReturn = p.pattern(returned, tail = Tail.STAR, mark = MarkSlot.STAR)
            assertTrue(runOne.summaries.demandEdges().any { (premise, facts) ->
                premise.members.singleOrNull()?.toPattern() == flowInput &&
                    flowReturn in f.ops.leaves(facts).toList()
            }, "The actual field write creates the run-1 STAR return demand")
            assertFalse(runOne.summaries.all().any { (_, facts) ->
                facts.layer == Layer.NORMAL && f.ops.leaves(facts).any { it.fact.base == returned }
            }, "No NORMAL run-1 return row can bypass the run-2 admission check")

            val runTwoInitials = f.processed.filter { it.run == 2 && it.method == helper }
                .flatMap { it.delta.premise.members }.map { it.toPattern() }
            assertContains(runTwoInitials, flowReturn,
                "Run-2 admits the requested STAR from its actual marked g descendant")
            val backwardResult = p.pattern(argument, tail = Tail.STAR, mark = MarkSlot.STAR,
                exclusion = ExclusionSet.of(written))
            assertTrue(f.records.byEntry(helper, flowReturn).any { record ->
                record.direction == Direction.BACKWARD && record.premise.toPattern() == flowReturn &&
                    record.conclusion.layer == Layer.NORMAL &&
                    backwardResult in f.ops.leaves(record.conclusion).toList()
            }, "The normal backward record retains the sibling exclusion and suffix correlation")
            assertTrue(f.configs[2].seeds.allowsSource(root, p.inst(root, 0), source),
                "The backward run reaches the real source and enables it in run-3")
            assertEquals(0L, f.results.last().demandLayerEdges)
        }
    }

}
