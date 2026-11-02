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

class LoopBlockBoundaryLimitTest {
    @Test fun `saved BL growth is globally limited before storing or offering its child result`() {
        // x.f=x; while(again()) { x=x; } normalExit.
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(2, 3), emptyList(), emptyList()),
            normalExit = 3, exceptionalExit = 4).use { f ->
            val x = AccessPathBase.Argument(0)
            val field = f.field("f")
            val t = MarkSlot.Concrete(f.mark("T"))
            f.statement(1, MicroEdgeBuilder().apply {
                write(x, listOf(field), weak = false, values = listOf(x), aliasPaths = emptyList())
            }.build())
            f.statement(2, MicroEdgeBuilder().apply { move(x, x) }.build())
            val layout = f.contexts.blockLayout(f.key)
            val tree = layout[layout.root]
            val blEntry = PortId.ROOT_ENTRY
            val loopEntry = layout.port(1, 2)!!.id
            val repeat = layout.port(2, 2)!!.id
            val leave = layout.normalExitForRoute(layout.port(2, 3)!!.id)!!.id
            val identity = f.manager.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
            val identityImage = f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR)
            // The prior run-3 limit 2 can retain this NORMAL field-write row.
            f.records.add(Record(f.key, Direction.FORWARD,
                f.manager.initial(f.pattern(x, listOf(field), Tail.STAR, MarkSlot.STAR)),
                f.fact(x, List(2) { field }, Tail.STAR, MarkSlot.STAR),
                BlockScope(tree.before!!, blEntry), loopEntry))
            for (entry in listOf(loopEntry, repeat)) for (exit in listOf(repeat, leave))
                f.records.add(Record(f.key, Direction.FORWARD, identity, identityImage,
                    BlockScope(tree.loop!!, entry), exit))
            f.records.add(Record(f.key, Direction.FORWARD, identity, identityImage,
                BlockScope(tree.after!!, leave), PortId.ROOT_EXIT))
            val need = f.pattern(x, List(3) { field }, Tail.ANY, t)
            val actual = f.fact(x, List(4) { field }, Tail.EXACT, t)
            val original = f.manager.initial(f.pattern(x, List(4) { field }, Tail.EXACT, t))
            val demand = DemandStore.Builder(f.manager).also { builder ->
                builder.add(f.key, DemandPattern(original.toPattern(), need))
                for (entry in listOf(loopEntry, repeat)) for (exit in listOf(repeat, leave))
                    builder.add(f.key, BlockScope(tree.loop!!, entry), exit, DemandPattern(need, need))
            }.build()
            val actor = f.core(index = 5, L = 4, demand = demand)
            f.submitRestricted(actor, actual)
            f.drain(actor, quantum = 1)
            val runtime = actor.blockRuntime!!
            val inputs = ArrayList<Pair<PremiseKey, Facts>>()
            for ((scope, _) in runtime.states()) if (scope.block == tree.loop)
                runtime.forEachLocalInput(scope) { link, value -> inputs += link.original to value }
            assertTrue(inputs.isNotEmpty(), "The control must retain an actual current loop subscription")
            for ((premise, facts) in inputs) {
                assertEquals(original, premise, "The global boundary cut preserves the complete parent original")
                assertEquals(Layer.DEMAND, facts.layer)
                assertTrue(f.ops.leaves(facts).all { it.fact.path.count { accessor -> accessor.isCounted() } <= 4 })
                assertTrue(f.ops.leaves(facts).all { it.fact.tail == Tail.ANY },
                    "The five-field BL composition must reach L as four-field MAY/DEMAND")
            }
            assertTrue(actor.summaries.all().all { (_, facts) -> f.ops.leaves(facts).all {
                it.fact.path.count { accessor -> accessor.isCounted() } <= 4
            } })
        }
    }
}
