package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

class KilledStaticExitCaptureTest {
    @Test fun `normal exit input is retained as guidance after its executable image is killed`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val mark = MarkSlot.Concrete(f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP))
            val original = f.manager.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = mark))
            val value = f.fact(STATIC, path, Tail.EXACT, mark, layer = Layer.DEMAND)
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val actor = f.core()
            actor.routeStaticResultToExit(f.inst(1), original, value)
            f.drain(actor)
            assertTrue(actor.summaries.all().none())
            val frozen = actor.freezeStaticWriteCandidates()
            assertSame(original, frozen.lostRows().single().original)
            assertEquals(f.ops.leaves(value).single(), frozen.lostRows().single().result)
            assertEquals(f.key, frozen.owner)
        }
    }

    @Test fun `intermediate exit write is observed before a continuation drops the result`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val original = f.manager.zero
            val value = f.fact(STATIC, path, Tail.EXACT, MarkSlot.Concrete(f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP)), layer = Layer.DEMAND)
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(2)))
            val at = OperationInput(ResumeSite.BoundaryInput(operation, false), original, Reach.NORMAL)
            val actor = f.core()
            var continued = false
            actor.emitOperationResult(at, StaticOperation.Write(operation, f.ops.leaves(value).single()), value) { _, _ ->
                continued = true // The next cleaner emits no result.
            }
            assertTrue(continued)
            assertTrue(actor.edges.edgesAt(f.inst(2)).none(), "An exit action must not reschedule NormalExit")
            assertTrue(actor.summaries.all().none())
            f.drain(actor)
            val frozen = actor.freezeStaticWriteCandidates()
            assertSame(original, frozen.lostRows().single().original)
            assertEquals(f.ops.leaves(value).single(), frozen.lostRows().single().result)
        }
    }

    @Test fun `final transformed exit result is observed and exact survivors are pruned`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val from = listOf(cls, f.field("f")); val to = listOf(cls, f.field("g"))
            val mark = MarkSlot.Concrete(f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP))
            val original = f.manager.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = mark))
            val value = f.fact(STATIC, from, Tail.STAR, mark, layer = Layer.DEMAND)
            val transfer = starEdge(STATIC, from, STATIC, to)
            // No local write descriptor: this exercises the final pre-filter observer.
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), listOf(MicroEdge.of(transfer)),
                emptyList(), emptyMap()), StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val actor = f.core()
            actor.routeStaticResultToExit(f.inst(1), original, value)
            f.drain(actor)
            val frozen = actor.freezeStaticWriteCandidates()
            assertEquals(setOf(from, to), frozen.observedRows().map { it.result.fact.path }.toSet())
            assertEquals(listOf(from), frozen.lostRows().map { it.result.fact.path }.toList())
            assertTrue(actor.summaries.all().any { (_, facts) -> f.ops.leaves(facts).any { it.fact.path == to } })
        }
    }

    @Test fun `exceptional boundary does not create normal guidance candidates`() {
        MethodAnalysisFixtures(listOf(listOf(1, 2), emptyList(), emptyList()), normalExit = 1, exceptionalExit = 2).use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val value = f.fact(STATIC, path, Tail.EXACT, MarkSlot.Concrete(f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP)), layer = Layer.DEMAND)
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(2)))
            val actor = f.core()
            actor.emitOperationResult(OperationInput(ResumeSite.BoundaryInput(operation, false), f.manager.zero, Reach.NORMAL),
                StaticOperation.Write(operation, f.ops.leaves(value).single()), value) { _, _ -> }
            assertEquals(0, actor.freezeStaticWriteCandidates().observedCount)
        }
    }

    @Test fun `late boundary resume is captured without normal exit rescheduling`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val mark = MarkSlot.Concrete(f.manager.marks.runtimeAtom(f.mark("T"), MarkMode.GROUP))
            val initial = f.manager.initial(f.pattern(STATIC, path, Tail.STAR, mark))
            val value = f.fact(STATIC, path, Tail.STAR, mark, layer = Layer.DEMAND)
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap()),
                StatementSummary.EMPTY, emptyList()), false, emptySet()))
            val operation = OperationId(FormKey(FormOwner(), f.key.method, f.key, f.inst(2)))
            val actor = f.core()
            actor.installPoint(initial, value, ResumeSite.BoundaryInput(operation, false))
            f.drain(actor)
            val frozen = actor.freezeStaticWriteCandidates()
            assertSame(initial, frozen.lostRows().single().original)
            assertTrue(f.processed.isEmpty(), "A boundary resume must not re-enter the statement worklist")
        }
    }
}
