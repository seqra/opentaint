package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class LoopBlockSavedIdentityTest {
    @Test fun `a growing saved loop result uses the boundary only AL identity and enclosing paired demand`() {
        // entry; while(again()) { x.f=x; } normalExit. The actual no-op entry
        // and exit transfers belong to the saved BL and AL spans.
        MethodAnalysisFixtures(listOf(listOf(1), listOf(1, 2), emptyList(), emptyList()),
            normalExit = 2, exceptionalExit = 3).use { f ->
            val x = AccessPathBase.Argument(0)
            val field = f.field("f")
            val t = MarkSlot.Concrete(f.mark("T"))
            f.statement(1, MicroEdgeBuilder().apply {
                write(x, listOf(field), weak = false, values = listOf(x), aliasPaths = emptyList())
            }.build())
            val layout = f.contexts.blockLayout(f.key)
            val root = layout[layout.root]
            val inputPort = layout.port(0, 1)!!.id
            val outputPort = layout.normalExitForRoute(layout.port(1, 2)!!.id)!!.id
            val identity = f.manager.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
            val identityImage = f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR)
            f.records.add(Record(f.key, Direction.FORWARD, identity, identityImage,
                BlockScope(root.before!!, PortId.ROOT_ENTRY), inputPort))
            f.records.add(Record(f.key, Direction.FORWARD,
                f.manager.initial(f.pattern(x, listOf(field), Tail.STAR, MarkSlot.STAR)),
                f.fact(x, listOf(field, field), Tail.STAR, MarkSlot.STAR),
                BlockScope(root.loop!!, inputPort), outputPort))
            f.records.add(Record(f.key, Direction.FORWARD, identity, identityImage,
                BlockScope(root.after!!, outputPort), PortId.ROOT_EXIT))
            val demand = DemandStore.Builder(f.manager).also {
                it.add(f.key, DemandPattern(f.pattern(x, listOf(field), Tail.EXACT, t),
                    f.pattern(x, listOf(field), Tail.ANY, t)))
            }.build()
            // Run-3 (limit 2) can produce the stored two-field NORMAL row.
            // Run-5 replays it at limit 4; paired B demand still selects depth 2.
            val actor = f.core(index = 5, L = 4, demand = demand)
            f.submitRestricted(actor, f.fact(x, listOf(field), Tail.EXACT, t))
            f.drain(actor, quantum = 1)
            val normal = actor.summaries.all().filter { it.second.layer == Layer.NORMAL }.toList()
            assertTrue(normal.any { (_, facts) -> f.ops.leaves(facts).any {
                it == f.pattern(x, listOf(field, field), Tail.EXACT, t)
            } }, "The growing result is useful through AL saved identity and B C5")
            assertTrue(f.processed.isEmpty(),
                "Genuine saved BL/L/AL spans include both original endpoint transfers")
            val runtime = actor.blockRuntime!!
            assertEquals(1, runtime.states().size, "Empty local C2 allocates no child transfer state")
            assertTrue(runtime.diagnosticStatistics().contains("rawFallbacks=1"))
            assertTrue(runtime.diagnosticStatistics().contains("drops=0"))
        }
    }
}
