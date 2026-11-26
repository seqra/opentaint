package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/**
 * R2 of spec/backward-condition-progress-implementation.md §5.7 (3)-(5): the capture tree of the forward run and
 * the refined seeds of the next backward run (spec backward-condition-progress §I.3, §II.4).
 */
class RefinedSeedIterationTest {
    private val owner = FormOwner()
    private val reportRule = object : CommonTaintConfigurationSink {
        override val id = "refined sink"
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = "refined sink"
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private val result = AccessPathBase.Return

    // ---- (3) End to end: program PG of spec §I.2 ----------------------------------------------------------------

    /**
     * main(): v = source() taints v.f1..fd (depth d); use(v). use(x): sink(x), rule `x.[any](T)` (unary).
     * Run 1 starts `use` with the abstract x.*, so run 1 captures only the root leaf and run 2 seeds the literal.
     * From run 3, each forward run cuts one field deeper (C2) and captures that field, and each backward run seeds
     * one field deeper: run 2k seeds x.f1..f(k-1).[any](T). Run 2d+1 sees the exact fact: the finding is confirmed.
     * Measured on R1 alone (no capture tree): the seed is x.[any](T) in each round, but the forward start follows
     * the K schedule, so the forward facts, the confirmed finding and run 2d+1 are the same. In this program the
     * capture tree changes only the backward seeds (spec §I.2 expects a provisional CURRENT finding).
     */
    @Test fun `PG the capture tree deepens the seed in each round and the finding is confirmed`() {
        for (depth in 1..3) DriverFixtures().use { f ->
            val p = f.program
            val v = AccessPathBase.LocalVar(0)
            val mark = MarkSlot.Concrete(p.mark("T"))
            val fields = listOf("f", "g", "h").take(depth).map(p::field)
            val main = p.method("main", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val use = p.method("use", listOf(listOf(1), emptyList()), 1).key()
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP, PathEdge(ZERO_FACT,
                PathFact(v, fields, Tail.EXACT, mark), ExclusionSet.Empty)), StatementSummary.EMPTY, emptyList()))
            p.call(main, 1, CallPlan(setOf(v), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(v, emptyList(), x, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(use)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP)),
            ), emptyList(), BEFORE, AFTER))
            val literal = p.pattern(x, tail = Tail.ANY, mark = mark)
            val sink = SinkRule(f.rule("contains T"), 0, listOf(literal), emptyList())
            p.exit(use, 1, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))

            val report = f.driver(HardRunLimitPolicy(IncreasingLimits, 11), 60.seconds, run1MarkMode = MarkMode.FULL)
                .analyze(listOf(main))

            assertEquals(RunStatus.COMPLETE, report.end.status, "depth=$depth")
            assertEquals(1, report.entries.size, "depth=$depth")
            assertFalse(report.entries.single().provisional, "depth=$depth: the refined demand reaches the exact fact")
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason, "depth=$depth")
            assertEquals(2 * depth + 1, report.end.run, "depth=$depth: one field per round")
            val exit = p.inst(use, 1)
            val seeds = f.processed.filter { it.run % 2 == 0 && it.method == use && it.delta.node == exit && it.delta.premise.isZero }
                .groupBy { it.run }
                .mapValues { (_, rows) -> methodLeaves(f.ops, rows.map { it.delta.facts }).filterTo(HashSet()) { it.fact.base == x } }
            val expected = (1..depth).associate { k ->
                2 * k to setOf(Conclusion(PathFact(x, fields.take(k - 1), Tail.ANY, mark), ExclusionSet.Empty, true))
            }
            assertEquals(expected, seeds, "depth=$depth")
        }
    }

    // ---- (3) The backward seed with and without a tree ----------------------------------------------------------

    private fun backwardSinkSeeds(tree: Boolean, literalTail: Tail = Tail.ANY): Set<Conclusion> = MethodAnalysisFixtures().use { f ->
        val fieldF = f.field("f")
        val fieldG = f.field("g")
        val literal = f.pattern(x, tail = literalTail)
        val sink = SinkRule(reportRule, 0, listOf(literal), emptyList())
        f.exitRules(2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
        val trees = if (!tree) emptyMap() else {
            val captures = org.opentaint.dataflow.bidi.store.CaptureTreeStore(f.manager)
            val key = CaptureKey(f.key, f.inst(2), sink.rule, literal)
            captures.addSink(key, f.fact(x, listOf(fieldF, fieldG), Tail.EXACT))
            captures.sinkTrees()
        }
        val seeds = SeedIndex(mapOf((f.key to f.inst(2)) to listOf(Seed.Sink(sink.rule, f.key, f.inst(2), literal))), trees)
        lateinit var service: RunMethodLocalServices
        f.core(index = 2, seeds = seeds,
            localFactory = MethodLocalServicesFactory { actor -> RunMethodLocalServices(actor).also { service = it } })
        val emitted = ArrayList<Facts>()
        service.fireSinkSeeds(f.inst(2), emitted::add)
        methodLeaves(f.ops, emitted)
    }

    @Test fun `a sink tree replaces the any literal by its leaves and no tree keeps the literal`() {
        MethodAnalysisFixtures().use { f ->
            val mark = MarkSlot.Concrete(f.mark("T"))
            // K = 1 in run 2: the tree leaf x.f.g.$ is cut to x.f.[any] by the CURRENT Cut.SEED.
            assertEquals(setOf(Conclusion(PathFact(x, listOf(f.field("f")), Tail.ANY, mark), ExclusionSet.Empty, true)),
                backwardSinkSeeds(tree = true))
            assertEquals(setOf(Conclusion(PathFact(x, emptyList(), Tail.ANY, mark), ExclusionSet.Empty, true)),
                backwardSinkSeeds(tree = false))
        }
    }

    /**
     * t5 of spec §II.4: the ND predicate sink `a.$(T) and b.[any](U)` with the inputs b.f.$(U) and b.g.h.$(U).
     * The forward predicate callback stores one tree for literal 1; the backward run seeds a.$(T) DEMAND (R1, K3)
     * and the two field chains of b in place of b.[any](U). Run 4 has K = 3, so no seed cut applies.
     */
    @Test fun `t5 an ND predicate sink seeds its exact literal DEMAND and the tree leaves of its any literal`() =
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val builder = RulePredicate.Builder(f.cancellation)
            val exactLeaf = builder.leaf(f.pattern(x, mark = t))
            val anyLeaf = builder.leaf(f.pattern(y, tail = Tail.ANY, mark = u))
            val predicate = builder.build(builder.and(listOf(exactLeaf, anyLeaf)))
            val id = RuleOccurrenceId(FormKey(owner, f.key.method, f.key, f.inst(2)), RuleKind.CALL_SINK, 0)
            val sink = SinkRule(reportRule, 0, predicate.leaves, emptyList(), id, predicate)
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val fieldF = f.field("f")
            val fieldG = f.field("g")
            val fieldH = f.field("h")

            val (actor, forward) = services(f, run1Full(f))
            assertTrue(forward.checkSinks(f.manager.zero, f.inst(2), f.fact(x, mark = t), listOf(sink)).fired.isEmpty())
            assertEquals(1, forward.checkSinks(f.manager.zero, f.inst(2), f.fact(y, listOf(fieldF), mark = u), listOf(sink)).fired.size)
            assertEquals(1, forward.checkSinks(f.manager.zero, f.inst(2), f.fact(y, listOf(fieldG, fieldH), mark = u), listOf(sink)).fired.size)
            val captures = assertNotNull(actor.captures).sinkTrees()
            val literal = predicate.leaves.first { it.fact.tail == Tail.ANY }
            assertEquals(setOf(CaptureKey(f.key, f.inst(2), id, literal)), captures.keys, "only the [any] literal is captured")
            assertEquals(setOf(listOf(fieldF), listOf(fieldG, fieldH)), leafSet(f, captures.values.single()))

            val seeds = SeedIndex.of(listOf(Seed.PredicateSink(id, f.key, f.inst(2))), listOf(assertNotNull(actor.captures)), f.manager)
            val backward = RunConfig(4, 3, DemandStore.Builder(f.manager).build(), f.records, seeds, listOf(f.key))
            val (_, services) = services(f, backward)
            val emitted = ArrayList<Facts>()
            services.fireSinkSeeds(f.inst(2), emitted::add)
            assertEquals(setOf(
                Conclusion(PathFact(x, emptyList(), Tail.EXACT, t), ExclusionSet.Empty, true),
                Conclusion(PathFact(y, listOf(fieldF), Tail.EXACT, u), ExclusionSet.Empty, true),
                Conclusion(PathFact(y, listOf(fieldG, fieldH), Tail.EXACT, u), ExclusionSet.Empty, true),
            ), methodLeaves(f.ops, emitted))
        }

    // ---- (4), (5) Conditional sources: S3, S5, the run-1 cube, A7 and the A3 guard ------------------------------

    private fun source(f: MethodAnalysisFixtures, predicate: RulePredicate): SourceRuleOccurrence {
        val id = RuleOccurrenceId(FormKey(owner, f.key.method, f.key, f.inst(2)), RuleKind.CALL_SOURCE, 0)
        return SourceRuleOccurrence(id, predicate, listOf(SourceAction(ActionId(id, ActionRole.SOURCE, 0), f.pattern(result).fact)))
    }

    private fun predicate(f: MethodAnalysisFixtures, multi: Boolean): RulePredicate {
        val builder = RulePredicate.Builder(f.cancellation)
        val anyLeaf = builder.leaf(f.pattern(x, tail = Tail.ANY, mark = MarkSlot.Concrete(f.mark("U"))))
        if (!multi) return builder.build(anyLeaf)
        val exactLeaf = builder.leaf(f.pattern(y, mark = MarkSlot.Concrete(f.mark("V"))))
        return builder.build(builder.and(listOf(anyLeaf, exactLeaf)))
    }

    private fun services(f: MethodAnalysisFixtures, config: RunConfig): Pair<RunMethodAnalyzer, RunMethodLocalServices> {
        lateinit var service: RunMethodLocalServices
        val core = f.core(config, localFactory = MethodLocalServicesFactory { actor -> RunMethodLocalServices(actor).also { service = it } })
        return core to service
    }

    private fun run1Full(f: MethodAnalysisFixtures) =
        RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)

    /** The source input of the [any] leaf: x.h.$(U); of the exact leaf: y.$(V). */
    private fun inputs(f: MethodAnalysisFixtures) = listOf(
        x to f.fact(x, listOf(f.field("h")), Tail.EXACT, MarkSlot.Concrete(f.mark("U"))),
        y to f.fact(y, mark = MarkSlot.Concrete(f.mark("V"))))

    private fun forwardTree(f: MethodAnalysisFixtures, config: RunConfig, multi: Boolean): Pair<SourceRuleOccurrence, TaintNode?> {
        val source = source(f, predicate(f, multi))
        val (actor, services) = services(f, config)
        var fired = 0
        for ((base, value) in inputs(f).take(if (multi) 2 else 1))
            services.sourcePredicate(source, f.manager.initial(f.pattern(base)), value, f.inst(2), false) { _, _ -> fired++ }
        assertTrue(fired > 0, "the source fires")
        val captures = assertNotNull(actor.captures)
        val anyLeaf = source.predicate.leaves.first { it.fact.tail == Tail.ANY }
        assertEquals(setOf(CaptureKey(f.key, f.inst(2), source.id, anyLeaf)), captures.sourceTrees().keys)
        return source to captures.sourceTrees()[CaptureKey(f.key, f.inst(2), source.id, anyLeaf)]
    }

    private fun leafSet(f: MethodAnalysisFixtures, tree: TaintNode?): Set<List<Int>> = buildSet {
        f.manager.taintAlg.forEachLeaf(checkNotNull(tree), EMPTY_PATH) { sigma, leaf -> assertFalse(leaf.hasAny); add(sigma.toList()) }
    }

    @Test fun `A7 a fired unary any source edge stores its checked input`() = MethodAnalysisFixtures().use { f ->
        val (_, tree) = forwardTree(f, run1Full(f), multi = false)
        assertEquals(setOf(listOf(f.field("h"))), leafSet(f, tree))
    }

    @Test fun `C6 the run-1 cube of a multi source gives its inputs`() = MethodAnalysisFixtures().use { f ->
        val (_, tree) = forwardTree(f, run1Full(f), multi = true)
        assertEquals(setOf(listOf(f.field("h"))), leafSet(f, tree))
    }

    @Test fun `a restricted multi combination gives its inputs`() = MethodAnalysisFixtures().use { f ->
        val source = source(f, predicate(f, multi = true))
        val action = source.actions.single()
        val seeds = SeedIndex.of(source.predicate.leaves.map { leaf ->
            Seed.Source(f.key, f.inst(2), source.transfer(leaf, action, multi = true).forward, action.id)
        })
        val config = RunConfig(3, 2, DemandStore.Builder(f.manager).build(), f.records, seeds, listOf(f.key))
        val (_, tree) = forwardTree(f, config, multi = true)
        assertEquals(setOf(listOf(f.field("h"))), leafSet(f, tree))
    }

    /** S3 (unary) and S5 (multi): the backward run emits the tree seed at the reversed source (A3 guard passes). */
    @Test fun `S3 S5 the reversed any source literal becomes its tree seed`() {
        for (multi in listOf(false, true)) MethodAnalysisFixtures().use { f ->
            val (source, tree) = forwardTree(f, run1Full(f), multi)
            val anyLeaf = source.predicate.leaves.first { it.fact.tail == Tail.ANY }
            val seeds = SeedIndex(emptyMap(), sourceTrees = mapOf(CaptureKey(f.key, f.inst(2), source.id, anyLeaf) to checkNotNull(tree)))
            val backward = RunConfig(2, 1, DemandStore.Builder(f.manager).build(), f.records, seeds, listOf(f.key))
            val (_, services) = services(f, backward)
            val emitted = ArrayList<Facts>()
            services.sourcePredicate(source.reversed(), f.manager.zero, f.fact(result), f.inst(2), false) { _, value -> emitted += value }
            val u = MarkSlot.Concrete(f.mark("U"))
            val refined = Conclusion(PathFact(x, listOf(f.field("h")), Tail.EXACT, u), ExclusionSet.Empty, true)
            val leaves = methodLeaves(f.ops, emitted.filter { it.base == x })
            assertEquals(setOf(refined), leaves, "multi=$multi")
        }
    }

    @Test fun `no source tree keeps the reversed literal`() = MethodAnalysisFixtures().use { f ->
        val source = source(f, predicate(f, multi = false))
        val backward = RunConfig(2, 1, DemandStore.Builder(f.manager).build(), f.records, SeedIndex.EMPTY, listOf(f.key))
        val (_, services) = services(f, backward)
        val emitted = ArrayList<Facts>()
        services.sourcePredicate(source.reversed(), f.manager.zero, f.fact(result), f.inst(2), false) { _, value -> emitted += value }
        assertEquals(setOf(Conclusion(PathFact(x, emptyList(), Tail.ANY, MarkSlot.Concrete(f.mark("U"))), ExclusionSet.Empty, true)),
            methodLeaves(f.ops, emitted))
    }
}
