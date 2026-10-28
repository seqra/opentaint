package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.CallerRef
import kotlin.test.*

/** Concrete entries below are produced by ordinary actual-input/request admission. */
class LocalStaticWriteSupplyTest {
    private fun actualWrite(mode: MarkMode, changeMark: Boolean, killAtExit: Boolean) = MethodAnalysisFixtures().use { f ->
        val arg = AccessPathBase.Argument(0)
        val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
        val input = f.manager.marks.runtimeAtom(f.mark("input"), mode)
        val output = if (changeMark) f.manager.marks.runtimeAtom(f.mark("output"), mode) else input
        val form = FormKey(FormOwner(), f.key.method, f.key, f.inst(0))
        val operation = OperationId(form)
        if (changeMark) {
            val occurrence = RuleOccurrenceId(form, RuleKind.CALL_SOURCE, 0)
            val action = ActionId(occurrence, ActionRole.SOURCE, 0)
            val target = f.pattern(STATIC, path, Tail.EXACT, MarkSlot.Concrete(output))
            val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
            val predicate = builder.build(builder.leaf(f.pattern(arg, mark = MarkSlot.Concrete(input))))
            f.statement(0, StatementSummary(setOf(arg), listOf(MicroEdge.of(keepEdge(arg))), emptyList(), emptyMap(),
                sources = listOf(SourceRuleOccurrence(occurrence, predicate, listOf(SourceAction(action, target.fact)))),
                staticOperations = listOf(StaticOperation.Write(operation, target, action = action))))
        } else {
            val store = starEdge(arg, emptyList(), STATIC, path)
            f.statement(0, StatementSummary(setOf(arg), listOf(MicroEdge.of(store)), emptyList(), emptyMap(),
                staticOperations = listOf(StaticOperation.Write(operation, Pattern(store.to, ExclusionSet.Empty), store))))
        }
        if (killAtExit) f.exitRules(2, ExitRules(RuleStatement(
            StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
            StatementSummary.EMPTY, emptyList()), false, emptySet()))
        val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = mode)
        val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
        val flow = f.manager.initial(arg, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
        actor.addMarkRequest(flow, input)
        f.drain(actor)
        val actual = f.fact(arg, mark = MarkSlot.Concrete(input), layer = Layer.DEMAND)
        actor.addLink(CallerRef(f.store.key("real caller"), f.manager.zero, Layer.DEMAND, f.inst(0)),
            actual.layer, actual)
        f.drain(actor)
        assertTrue(actor.initials.all().contains(f.manager.initial(arg, null, Tail.EXACT,
            ExclusionSet.Empty, MarkSlot.Concrete(input))), "A concrete entry requires an actual matching answer")
        val service = checkNotNull(actor.runnerPort.staticService)
        val replies = service.commit(StaticBatch().apply {
            interests += StaticInterest(f.store.key("observer"), 1,
                f.pattern(STATIC, path, Tail.STAR, MarkSlot.STAR), (MarkSet.of(input) + MarkSet.of(output)))
        }).filterIsInstance<StaticOwnerEffect.PointReady>()
        assertEquals(listOf(MarkSet.of(output)), replies.map { it.supply.groups },
            "A local write supplies its computed output mark, before and independently of the exit")
        if (changeMark) assertNotEquals(input, output)
        else assertEquals(1, service.statistics().flowWriterRows,
            "The original p/FLOW -> C.f/FLOW writer remains after concrete supply")
        if (killAtExit) assertTrue(actor.summaries.all().none { it.second.base == STATIC },
            "Pool visibility does not fabricate an outgoing summary after an exit kill")
        assertEquals(1, service.statistics().suppliedGroups)
    }

    @Test fun `actual concrete input supplies local copy in FULL and GROUP before exit survival is known`() {
        for (mode in MarkMode.entries) for (kill in listOf(false, true)) actualWrite(mode, false, kill)
    }

    @Test fun `a completed color changing local action supplies output in FULL and GROUP despite exit kill`() {
        for (mode in MarkMode.entries) actualWrite(mode, true, true)
    }
}
