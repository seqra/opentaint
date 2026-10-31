package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.RunConfig
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*

class SelectedFullReferenceTest {
    private val argument = AccessPathBase.Argument(0)
    private val returned = AccessPathBase.Return
    private fun summary(vararg edges: PathEdge) = StatementSummary(
        edges.map { it.from.base }.toSet(), edges.map(MicroEdge::of), emptyList(), emptyMap())
    private fun config(f: FiniteProgramFixtures, root: MethodKey, mode: MarkMode = MarkMode.FULL) =
        RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(root), run1MarkMode = mode)
    private fun inputs(root: MethodKey) = ProgramRunInputs(listOf(root), emptyList(), emptyList(), emptyList())

    @Test fun `selected FULL oracle preserves source layers and full marks while old snapshots stay unchanged`() {
        for (tail in listOf(Tail.EXACT, Tail.ANY_TAINT, Tail.ANY)) FiniteProgramFixtures().use { f ->
            val key = f.method("source", listOf(listOf(1), emptyList()), 1).key()
            val t = f.mark("T")
            val source = PathEdge(ZERO_FACT, PathFact(returned, emptyList(), tail, MarkSlot.Concrete(t)), ExclusionSet.Empty)
            f.entry(key, RuleStatement(summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            val selectedConfig = config(f, key)
            val selected = NaiveClosure(f, selectedConfig, semantics = NaiveClosure.Semantics.SELECTED, rawInputs = inputs(key)).run()
            val actual = ProductionSchedule(f, selectedConfig).run()
            assertEquals(actual.rawSummaries, selected.rawSummaries, "FULL source tail=$tail")
            val expected = ObservedEdge(key, setOf(ZERO_PATTERN),
                Conclusion(source.to, ExclusionSet.Empty, demand = tail == Tail.ANY))
            assertContains(selected.rawSummaries, expected)
            val old = NaiveClosure(f, selectedConfig, semantics = NaiveClosure.Semantics.PRE_TARGETS, rawInputs = inputs(key)).run()
            val grouped = GroupedScalarMarks(f.manager.marks).conclusion(expected.conclusion)
            assertContains(old.rawSummaries, expected.copy(conclusion = grouped), "PRE_TARGETS keeps its old GROUP projection")
            val historical = NaiveClosure(f, selectedConfig, semantics = NaiveClosure.Semantics.HISTORICAL, rawInputs = inputs(key)).run()
            assertContains(historical.rawSummaries, expected, "The historical scalar source table is unchanged")
            val selectedGroup = NaiveClosure(f, config(f, key, MarkMode.GROUP),
                semantics = NaiveClosure.Semantics.SELECTED, rawInputs = inputs(key)).run()
            assertContains(selectedGroup.rawSummaries, expected.copy(conclusion = grouped), "Explicit GROUP remains DEMAND")
        }
    }

    @Test fun `selected FULL oracle uses ordinary EXACT and STAR start layers and preserves full requests`() {
        for (childInput in listOf(false, true)) FiniteProgramFixtures().use { f ->
            val root = f.method("caller", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val callee = f.method("callee", listOf(listOf(1), emptyList()), 1).key()
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val sourcePath = if (childInput) listOf(f.field("f")) else emptyList()
            val source = PathEdge(ZERO_FACT, PathFact(argument, sourcePath, Tail.EXACT, t), ExclusionSet.Empty)
            f.entry(root, RuleStatement(summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            val transfer = PathEdge(PathFact(argument, emptyList(), Tail.EXACT, t),
                PathFact(returned, emptyList(), Tail.EXACT, u), ExclusionSet.Empty)
            f.entry(callee, RuleStatement(summary(ZERO_KEEP, transfer), StatementSummary.EMPTY, emptyList()))
            f.call(root, 1, CallPlan(setOf(argument, returned), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, summary(keepEdge(argument), ZERO_KEEP)),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, summary(keepEdge(returned), ZERO_KEEP)),
            ), emptyList(), BEFORE, AFTER))
            val selectedConfig = config(f, root)
            val selected = NaiveClosure(f, selectedConfig, semantics = NaiveClosure.Semantics.SELECTED, rawInputs = inputs(root)).run()
            val actual = ProductionSchedule(f, selectedConfig).run()
            assertEquals(actual.rawSummaries, selected.rawSummaries)
            val expectedInitial = Pattern(transfer.from.copy(tail = if (childInput) Tail.STAR else Tail.EXACT), ExclusionSet.Empty)
            assertContains(selected.initials, ObservedInitial(callee, expectedInitial))
            assertContains(selected.rawSummaries, ObservedEdge(callee, setOf(expectedInitial),
                Conclusion(transfer.to, ExclusionSet.Empty, demand = childInput)))
            assertTrue(selected.requests.any { it.kind == ReferenceRequestKind.Mark(t.mark) })
            assertTrue(selected.rawSummaries.filter { it.method == callee && it.conclusion.fact.mark == u }
                .all { it.conclusion.demand == childInput },
                "FULL retains natural layers: exact starts NORMAL; STAR starts remain DEMAND")
        }
    }
}
