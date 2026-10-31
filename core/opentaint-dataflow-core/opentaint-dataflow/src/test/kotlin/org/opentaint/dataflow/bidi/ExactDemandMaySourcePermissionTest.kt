package org.opentaint.dataflow.bidi

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

/** Exact FULL sources use ordinary native replay. C2 permission remains separate. */
class ExactDemandMaySourcePermissionTest {
    private data class Case(val root: MethodKey, val factory: MethodKey, val rhs: AccessPathBase,
                            val u: MarkSlot.Concrete, val source: PathEdge?, val sink: SinkRule)

    private fun program(f: DriverFixtures, depth: Int, uncertainCondition: Boolean = false): Case {
        val root = f.program.method("main depth $depth", listOf(listOf(1), listOf(2), listOf(3), listOf(4), emptyList()), 4).key()
        val factory = f.program.method("factory depth $depth", listOf(listOf(1), emptyList()), 1).key()
        val rhs = AccessPathBase.LocalVar(0)
        val temporary = AccessPathBase.LocalVar(1)
        val condition = AccessPathBase.LocalVar(2)
        val arg = AccessPathBase.Argument(0)
        val out = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val path = listOf(f.program.field("a"), f.program.field("b")).take(depth)
        val u = MarkSlot.Concrete(f.program.mark("U"))
        val source = if (uncertainCondition) null else
            PathEdge(ZERO_FACT, PathFact(ret, emptyList(), Tail.EXACT, u), ExclusionSet.Empty)
        if (source != null) f.program.entry(factory,
            RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
        else {
            // Genuine uncertainty is retained: CM(p,T) has only a MAY input.
            // The source action assigns U at an exact result but keeps DEMAND.
            val t = MarkSlot.Concrete(f.program.mark("T"))
            val maySource = PathEdge(ZERO_FACT, PathFact(condition, emptyList(), Tail.ANY, t), ExclusionSet.Empty)
            f.program.entry(root, RuleStatement(f.summary(ZERO_KEEP, maySource), StatementSummary.EMPTY, emptyList()))
            val builder = RulePredicate.Builder(f.cancellation)
            val predicate = builder.build(builder.leaf(f.program.pattern(arg, mark = t)))
            val id = RuleOccurrenceId(FormKey(FormOwner(), factory.method, factory,
                f.program.inst(factory, 0)), RuleKind.CALL_SOURCE, 0)
            val action = SourceAction(ActionId(id, ActionRole.SOURCE, 0),
                f.program.pattern(ret, mark = u).fact)
            f.program.statement(factory, 0, StatementSummary(setOf(arg), listOf(MicroEdge.of(ZERO_KEEP)),
                emptyList(), emptyMap(), sources = listOf(SourceRuleOccurrence(id, predicate, listOf(action)))))
        }
        val bindIn = if (uncertainCondition) f.summary(ZERO_KEEP,
            starEdge(condition, emptyList(), arg, emptyList())) else f.summary(ZERO_KEEP)
        f.program.call(root, 1, CallPlan(setOf(rhs, condition), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, bindIn),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Callees(ADDED, RETURNED, listOf(factory)),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK,
                f.summary(ZERO_KEEP, starEdge(ret, emptyList(), rhs, emptyList()))),
        ), emptyList(), BEFORE, AFTER))
        f.program.statement(root, 2, MicroEdgeBuilder().apply {
            if (depth == 1) write(out, path, weak = false, values = listOf(rhs), aliasPaths = emptyList())
            else write(temporary, path.takeLast(1), weak = false, values = listOf(rhs), aliasPaths = emptyList())
        }.build())
        if (depth == 2) f.program.statement(root, 3, MicroEdgeBuilder().apply {
            write(out, path.take(1), weak = false, values = listOf(temporary), aliasPaths = emptyList())
        }.build())
        val sink = SinkRule(f.rule("sink U"), 0, listOf(f.program.pattern(out, path, mark = u)), emptyList())
        f.program.exit(root, 4, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(sink)), false, emptySet()))
        return Case(root, factory, rhs, u, source, sink)
    }

    @Test fun `normal exact FULL source is saved and replays across a cut caller without source permission`() {
        for (depth in listOf(1, 2)) DriverFixtures().use { f ->
            val c = program(f, depth)
            val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL).analyze(listOf(c.root))
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals(if (depth == 1) listOf(1) else listOf(1, 2, 3), f.configs.map { it.index })
            val exact = f.program.pattern(AccessPathBase.Return, mark = c.u)
            val run1 = f.results.first().analyzers.single { it.key == c.factory }
            assertTrue(run1.summaries.all().any { (p, facts) -> p.isZero && facts.layer == Layer.NORMAL &&
                exact in f.ops.leaves(facts).toList() })
            assertTrue(run1.summaries.demandEdges().none { (p, facts) -> p.isZero && exact in f.ops.leaves(facts).toList() },
                "A known exact FULL source is not a demand")
            assertTrue(f.records.byExit(c.factory, exact).any { it.direction == Direction.FORWARD &&
                it.premise.isZero && it.conclusion.layer == Layer.NORMAL && exact in f.ops.leaves(it.conclusion).toList() })
            assertEquals(c.sink.rule, report.entries.single().descriptor.rule)
            if (depth == 2) {
                val incoming = checkNotNull(f.configs[1].demand)
                assertTrue(incoming.explicitRows(c.factory).isEmpty(), "The saved NORMAL source has no current demand row")
                val may = exact.copy(fact = exact.fact.copy(tail = Tail.ANY))
                val actual = f.manager.factsOf(may.fact, may.exclusion, Layer.DEMAND)
                val offered = f.processed.filter { it.run == 2 && it.method == c.root && it.delta.node == f.program.inst(c.root, 1) }
                    .flatMap { f.ops.leaves(it.delta.facts).toList() }
                assertTrue(offered.any { it.fact.base == c.rhs && it.fact.tail == Tail.ANY && it.fact.mark == c.u })
                assertTrue(incoming.initials(c.factory, actual, f.configs[1].admissionPolicy).isEmpty())
                assertTrue(f.configs[1].records.byExit(c.factory, may).any { record ->
                    record.reversedAt(may).any { view -> view.premise == exact && view.result.fact == ZERO_FACT }
                })
                assertTrue(f.results[1].recordCrossings > 0, "The backward native read is applied before current admission")
                assertTrue(f.results[1].analyzers.single { it.key == c.root }.outgoingTargets.any {
                    it.premise.isZero && it.target == Target.DemandTarget
                }, "The accepted reversed source result discharges to Target without a source hit")
                assertTrue(f.results.drop(1).all { run -> run.analyzers.none { it.key == c.factory } })
                assertTrue(f.links(2, c.factory).isEmpty() && f.links(3, c.factory).isEmpty(),
                    "A native effect does not admit a current callee input")
                val source = checkNotNull(c.source)
                assertTrue(f.results[1].analyzers.flatMap { it.sourceHits?.entries()?.toList().orEmpty() }
                    .none { it.first == c.factory && it.third == source })
                assertFalse(f.configs[2].seeds.allowsSource(c.factory, c.factory.statement, source))
                assertTrue(f.results[2].recordCrossings > 0, "The forward saved source supplies U without a Source seed")
                val exactGuide = DemandStore.Builder(f.manager).apply {
                    add(c.factory, DemandPattern(exact, ZERO_PATTERN))
                }.build()
                assertEquals(setOf(AdmittedInitial(f.manager.initial(exact), Layer.DEMAND)),
                    exactGuide.initials(c.factory, actual, f.configs[1].admissionPolicy),
                    "An explicit concrete exact guide can admit the cut input provisionally")
            }
        }
    }

    @Test fun `genuine DEMAND exact conditional result admits a cut caller provisionally without native bypass`() = DriverFixtures().use { f ->
        val c = program(f, 2, uncertainCondition = true)
        val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL).analyze(listOf(c.root))
        assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
        val exact = f.program.pattern(AccessPathBase.Return, mark = c.u)
        val run1 = f.results.first().analyzers.single { it.key == c.factory }
        assertTrue(run1.summaries.demandEdges().any { (_, facts) -> facts.layer == Layer.DEMAND &&
            exact in f.ops.leaves(facts).toList() }, "An exact conclusion does not remove uncertainty in its guard")
        assertTrue(f.records.byExit(c.factory, exact).none(), "There is no NORMAL exact producer to replay")
        val incoming = checkNotNull(f.configs[1].demand)
        assertTrue(incoming.explicitRows(c.factory).any { it.entry == exact })
        val may = exact.copy(fact = exact.fact.copy(tail = Tail.ANY))
        assertEquals(setOf(AdmittedInitial(f.manager.initial(exact), Layer.DEMAND)),
            incoming.initials(c.factory, f.manager.factsOf(may.fact, may.exclusion, Layer.DEMAND),
                f.configs[1].admissionPolicy))
        assertTrue(f.results[1].analyzers.any { it.key == c.factory })
        assertTrue(f.processed.any { it.run == 2 && it.method == c.factory &&
            it.delta.premise == f.manager.initial(exact) && it.delta.facts.layer == Layer.DEMAND },
            "The exact initial retains the cut caller's DEMAND layer through real delivery")
        assertTrue(report.entries.isEmpty(), "The provisional guard result is not a settled NORMAL report")
    }
}
