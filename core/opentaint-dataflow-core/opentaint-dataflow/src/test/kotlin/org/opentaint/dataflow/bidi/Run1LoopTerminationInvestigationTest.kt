package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

/** Production actor regressions for the former unchanged-fact feedback loop. */
class Run1LoopTerminationInvestigationTest {
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.LocalVar(0)

    private fun source(f: MethodAnalysisFixtures, owner: FormOwner, statement: Int,
                       from: AccessPathBase, to: AccessPathBase): SourceRuleOccurrence {
        val id = RuleOccurrenceId(FormKey(owner, f.key.method, f.key, f.inst(statement)), RuleKind.CALL_SOURCE, 0)
        val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
        val predicate = builder.build(builder.leaf(f.pattern(from)))
        val grouped = RulePredicate.Builder(f.cancellation, f.manager.marks)
        val groupedPredicate = grouped.build(grouped.leaf(f.run1Pattern(from)))
        return SourceRuleOccurrence(id, predicate,
            listOf(SourceAction(ActionId(id, ActionRole.SOURCE, 0), f.pattern(to).fact)),
            groupTransfers = true, unaryTransfers = listOf(SourceUnaryTransfer(groupedPredicate, f.pattern(from))))
    }

    private fun graph(loopSource: Boolean, plainCopy: Boolean = false, nonZero: Boolean = false,
                      duplicateInitial: Boolean = false,
                      observe: (MethodAnalysisFixtures, RunMethodAnalyzer) -> Unit) {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(2, 3), emptyList()), normalExit = 3).use { f ->
            val owner = FormOwner()
            val entry = listOf(ZERO_KEEP, PathEdge(ZERO_FACT, f.pattern(x).fact, ExclusionSet.Empty))
            f.entryRules(RuleStatement(StatementSummary(setOf(AccessPathBase.Zero), entry.map { MicroEdge.of(it) },
                emptyList(), emptyMap()), StatementSummary.EMPTY, emptyList()))
            if (plainCopy) {
                f.statement(1, StatementSummary(setOf(x), listOf(MicroEdge.of(
                    PathEdge(f.pattern(x).fact, f.pattern(y).fact, ExclusionSet.Empty))), emptyList(), emptyMap()))
                if (loopSource) f.statement(2, StatementSummary(setOf(y), listOf(MicroEdge.of(
                    PathEdge(f.pattern(y).fact, f.pattern(y).fact, ExclusionSet.Empty))), emptyList(), emptyMap()))
            } else {
                f.statement(1, StatementSummary(emptySet(), emptyList(), emptyList(), emptyMap(),
                    sources = listOf(source(f, owner, 1, x, y))))
                if (loopSource) f.statement(2, StatementSummary(setOf(y), emptyList(), emptyList(), emptyMap(),
                    sources = listOf(source(f, owner, 2, y, y))))
            }
            val initial = f.manager.initial(f.run1Pattern(x))
            val actor = f.core(localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            if (nonZero) {
                actor.addInitial(initial)
                if (duplicateInitial) actor.addInitial(initial)
            } else actor.addRootZero()
            observe(f, actor)
        }
    }

    @Test fun `conditional source self loop reaches an ordinary AP fixed point`() = checkLoop(plainCopy = false)
    @Test fun `plain marked copy self loop reaches an ordinary AP fixed point`() = checkLoop(plainCopy = true)
    @Test fun `a legal nonzero exact initial closes the same marked copy cycle`() =
        checkLoop(plainCopy = true, nonZero = true)
    @Test fun `a repeated actual initial does not reopen the closed cycle`() =
        checkLoop(plainCopy = true, nonZero = true, duplicateInitial = true)

    private fun checkLoop(plainCopy: Boolean, nonZero: Boolean = false, duplicateInitial: Boolean = false) {
        graph(loopSource = true, plainCopy = plainCopy, nonZero = nonZero,
            duplicateInitial = duplicateInitial) { f, actor ->
            closeWithinBound(f, actor)
            // Block admission adds an abstract FLOW companion and gives the
            // entry and repeat traversals independent post-statement stores.
            // Those are different relations, not reopening one marked cell.
            val seen = f.processed.filter { it.node.location.index == 2 && it.facts.base == y && it.facts is TaintTree }
            assertTrue(seen.isNotEmpty(), "The actual marked loop body must run")
            assertEquals(1, seen.map { f.ops.leaves(it.facts).toList() }.distinct().size,
                "Every marked traversal has the same concrete GROUP image")
            assertTrue(seen.all { it.facts.layer == Layer.DEMAND })
            val runtime = assertNotNull(actor.blockRuntime)
            val owner = runtime.layout.ownerOf(2)
            val cells = runtime.states().filter { it.first.block == owner }.flatMap { (scope, state) ->
                state.edges.edgesAt(f.inst(2)).map { (premise, facts) -> Triple(scope, premise, facts) }.toList()
            }
            assertTrue(cells.any { it.third.base == y && it.third is TaintTree })
            val keys = cells.map { (scope, premise, facts) -> Triple(scope, premise, facts.groupKey) }
            assertEquals(keys.size, keys.toSet().size,
                "One final packet per scope, post-S point, local initial and group")
            val processed = f.processed.size
            repeat(4) { assertTrue(actor.work(1)); f.pumpQuestions() }
            assertEquals(processed, f.processed.size, "An unchanged closed relation must remain quiescent")
        }
    }

    @Test fun `the acyclic source control still reaches the exit`() {
        graph(loopSource = false) { f, actor ->
            closeWithinBound(f, actor)
            assertTrue(f.processed.any { it.node.location.index == 3 && it.facts.base == y })
        }
    }

    private fun closeWithinBound(f: MethodAnalysisFixtures, actor: RunMethodAnalyzer) {
        var complete = false
        var quanta = 0
        while (!complete && quanta < 512) {
            quanta++
            val drained = actor.work(1)
            val delivered = f.pumpQuestions()
            complete = drained && !delivered
        }
        val detail = "quanta=$quanta physicalEvents=${f.processed.size} " +
            actor.blockRuntime?.diagnosticStatistics().orEmpty()
        println("LOOP_FIXED_POINT_CONTROL $detail")
        assertTrue(complete, "The finite GROUP relation must close within 512 counted work quanta; $detail")
        assertTrue(f.processed.size <= 64, "Local dispatch must not repeat unbounded physical work; $detail")
        assertTrue(actor.work(1), "The closed method remains idle; $detail")
    }
}
