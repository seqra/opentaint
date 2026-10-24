package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

/** Exercise the actual bulk actor branch; the usual fixture observers use its scalar fallback. */
class NeutralBatchEngineTest {
    private val argument = AccessPathBase.Argument(0)
    private val local = AccessPathBase.LocalVar(0)
    private val returned = AccessPathBase.Return

    private fun actor(f: MethodAnalysisFixtures, observe: Boolean): RunMethodAnalyzer {
        val field = f.field("field")
        f.statement(0, StatementSummary(setOf(argument),
            listOf(MicroEdge.of(starEdge(argument, listOf(field), local, emptyList()))), emptyList(), emptyMap()))
        f.statement(1, StatementSummary(setOf(local),
            listOf(MicroEdge.of(starEdge(local, emptyList(), returned, emptyList()))), emptyList(), emptyMap()))
        val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
        return f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices), observe = observe)
    }

    private fun initials(f: MethodAnalysisFixtures): List<InitialAp> = listOf("T", "U", "V").map { name ->
        f.manager.initial(argument, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.Concrete(f.mark(name)))
    }

    @Test
    fun `bulk actor respects quantum and retains all masks before its final barrier`() {
        MethodAnalysisFixtures().use { f ->
            val actor = actor(f, observe = false)
            val input = initials(f)
            input.forEach(actor::addInitial)
            assertFalse(actor.work(2))
            assertEquals(2, actor.steps)
            assertEquals(1, actor.neutralBatchApplications)
            assertEquals(2, actor.neutralBatchMemberships)
            assertFailsWith<IllegalStateException> { actor.freeze() }
            f.drain(actor, quantum = 2)
            val summaries = actor.summaries.all().filter { it.second.base == returned }.toList()
            assertEquals(input.toSet(), summaries.map { it.first }.toSet())
            for ((initial, facts) in summaries) {
                val mark = ((initial as InitialAp).mark as MarkSlot.Concrete).mark
                assertEquals(setOf(mark), f.ops.leaves(facts).map { (it.fact.mark as MarkSlot.Concrete).mark }.toSet())
                assertEquals(ExclusionSet.Empty, (facts as TaintTree).exclusion)
            }
            assertTrue(actor.neutralBatchMemberships >= 6, "Two plain statement stages retain all three marks")
            assertTrue(actor.neutralBulkStorePackets > 0, "The packed result reaches storage before scalar decoding")
            assertTrue(actor.neutralBulkStoreMemberships >= actor.neutralBulkStorePackets)
            assertEquals(9, actor.steps, "The exit is processed by the scalar boundary")
            actor.freeze()
        }
    }

    @Test
    fun `scalar observer fallback preserves the same final ordinary and protected relations`() {
        fun run(observe: Boolean): Pair<Set<String>, Long> = MethodAnalysisFixtures().use { f ->
            val actor = actor(f, observe)
            initials(f).forEach(actor::addInitial)
            f.drain(actor, quantum = 100)
            val outputs = actor.summaries.all().flatMap { (initial, facts) -> f.ops.leaves(facts).map { leaf ->
                val mark = (leaf.fact.mark as MarkSlot.Concrete).mark
                val original = ((initial as InitialAp).mark as MarkSlot.Concrete).mark
                "${f.manager.marks.key(original)}:${leaf.fact.base}:${leaf.fact.path}:${leaf.fact.tail}:${facts.layer}:${f.manager.marks.key(mark)}:${(facts as? TaintTree)?.nonSubsumable != null}"
            } }.toSet()
            if (observe) {
                assertTrue(f.processed.isNotEmpty())
                assertTrue(f.cuts.isNotEmpty())
                assertEquals(0, actor.neutralBatchApplications)
            } else assertTrue(actor.neutralBatchApplications > 0)
            outputs to actor.neutralBatchApplications
        }
        assertEquals(run(true).first, run(false).first)
    }

    @Test
    fun `a rule statement remains scalar and retains same mark demand in bulk enabled actor`() {
        MethodAnalysisFixtures().use { f ->
            val actor = actor(f, observe = false)
            val t = MarkSlot.Concrete(f.mark("T"))
            val builder = RulePredicate.Builder(f.cancellation)
            val condition = builder.build(builder.leaf(f.pattern(local, mark = t)))
            val id = RuleOccurrenceId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)), RuleKind.CALL_SOURCE, 0)
            val source = SourceRuleOccurrence(id, condition, listOf(SourceAction(ActionId(id, ActionRole.SOURCE, 0),
                PathFact(returned, emptyList(), Tail.EXACT, t))))
            f.statement(1, StatementSummary(setOf(local), emptyList(), emptyList(), emptyMap(), sources = listOf(source)))
            initials(f).forEach(actor::addInitial)
            f.drain(actor, quantum = 2)
            assertTrue(actor.neutralBatchApplications > 0)
            assertEquals(3, actor.neutralBatchMemberships, "Only the first plain statement can batch")
            assertTrue(actor.summaries.all().any { (_, facts) -> facts.base == returned &&
                f.ops.leaves(facts).any { it.fact.mark == t } })
            assertTrue(actor.summaries.all().filter { it.second.base == returned }
                .map { it.second }.filterIsInstance<TaintTree>().any { it.nonSubsumable != null })
        }
    }
}
