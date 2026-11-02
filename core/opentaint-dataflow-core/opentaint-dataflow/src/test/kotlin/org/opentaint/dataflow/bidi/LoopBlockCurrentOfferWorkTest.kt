package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.BlockScope
import kotlin.test.*

class LoopBlockCurrentOfferWorkTest {
    @Test fun `new root input reserves existing local summary deliveries without a new child initial`() {
        // Node m(Node p) { Node x=p; while (again()) { } return x; }
        // First infer ordinary FLOW rows. A later actual p/T input can use
        // those current rows even though no CM requests a new child T initial.
        val graph = listOf(listOf(1), listOf(2), listOf(3, 4), listOf(2), listOf(5), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 5).use { f ->
            val p = AccessPathBase.Argument(0)
            val x = AccessPathBase.LocalVar(0)
            val ret = AccessPathBase.Return
            f.statement(1, MicroEdgeBuilder().apply { move(x, p) }.build())
            f.statement(4, MicroEdgeBuilder().apply { move(ret, x) }.build())
            val actor = f.core(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL),
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            actor.addInitial(f.manager.initial(f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR)))
            f.drain(actor, quantum = 1)
            val runtime = assertNotNull(actor.blockRuntime)
            runtime.requireIdle()
            val before = checkNotNull(runtime.layout[runtime.layout.root].before)
            val child = runtime.states().single { (scope, _) -> scope.block == before }.second
            assertTrue(child.portSummaries.entries().any { (_, rows) -> rows.all().any { (_, facts) ->
                facts is FlowTree && facts.base == x
            } }, "The prefix must already own a real current p/FLOW -> x/FLOW summary")
            val oldInitials = child.initials.admissions().toList()
            val mark = MarkSlot.Concrete(f.mark("T"))
            val actualInitial = f.manager.initial(f.pattern(p, tail = Tail.EXACT, mark = mark))
            f.enqueued.clear()

            // A real later input enters the already idle original method. The
            // block's abstraction only reoffers its existing FLOW initial.
            actor.addInitial(actualInitial)
            assertEquals(oldInitials, child.initials.admissions().toList(),
                "No local CM means no fresh concrete child initial is emitted")
            assertTrue(f.enqueued.any { it === actor },
                "A fresh live input matching current local summaries needs counted method Work")
            f.drain(actor, quantum = 1)
            runtime.requireIdle()
            assertTrue(actor.summaries.all().any { (original, facts) ->
                original === actualInitial && facts.layer == Layer.NORMAL &&
                    f.ops.leaves(facts).any { it.fact.base == ret && it.fact.mark == mark && it.fact.tail == Tail.EXACT }
            }, "Existing FLOW summaries must transport the real later T input to the method return")
            assertTrue(runtime.states().filter { it.first != BlockScope.ROOT }.all { (_, state) ->
                state.initials.all().none { it.mark == mark }
            }, "The result must come from ordinary current-summary composition, not new concrete analysis")
            actor.freeze()
        }
    }
}
