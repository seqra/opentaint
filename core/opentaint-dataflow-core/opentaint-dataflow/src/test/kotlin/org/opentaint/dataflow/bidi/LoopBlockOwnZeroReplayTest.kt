package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Runtime seam tests. Saved rows and the current demand snapshot are explicit
 * component inputs. E21's separate driver test proves their full-program route. */
class LoopBlockOwnZeroReplayTest {
    private fun savedSource(opposite: Boolean) {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2), listOf(3, 4), listOf(2),
            listOf(5), emptyList(), emptyList()), normalExit = 5, exceptionalExit = 6).use { f ->
            val x = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val field = f.field("f")
            val mark = MarkSlot.Concrete(f.mark("T"))
            f.statement(3, MicroEdgeBuilder().apply { read(x, x, listOf(field)) }.build())
            f.statement(4, MicroEdgeBuilder().apply { move(ret, x) }.build())
            val layout = f.contexts.blockLayout(f.key)
            val tree = layout[layout.root]
            val before = checkNotNull(tree.before)
            val loop = checkNotNull(tree.loop)
            val after = checkNotNull(tree.after)
            val input = checkNotNull(layout.port(1, 2)).id
            val repeat = checkNotNull(layout.port(3, 2)).id
            val leave = checkNotNull(layout.normalExitForRoute(checkNotNull(layout.port(2, 4)).id)).id
            fun flow(base: AccessPathBase, path: List<Int> = emptyList()) =
                f.pattern(base, path, Tail.STAR, MarkSlot.STAR)
            fun save(scope: BlockScope, exit: PortId, p: Pattern, c: Facts, direction: Direction = Direction.FORWARD) {
                f.records.add(Record(f.key, direction, f.manager.initial(p), c, scope, exit))
            }
            save(BlockScope(before, PortId.ROOT_ENTRY), input, f.manager.zero.toPattern(), Reach.NORMAL)
            val sourceValue = f.fact(x, List(3) { field }, Tail.EXACT, mark)
            for (entry in listOf(input, repeat)) {
                if (opposite) {
                    // Effective opposite view: ZERO -> x.f.f.f.$/T, NORMAL.
                    save(BlockScope(loop, repeat), entry, f.ops.leaves(sourceValue).single(),
                        Reach.NORMAL, Direction.BACKWARD)
                } else save(BlockScope(loop, entry), repeat, f.manager.zero.toPattern(), sourceValue)
                val read = flow(x, listOf(field))
                save(BlockScope(loop, entry), repeat, read, f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR))
                save(BlockScope(loop, entry), leave, flow(x), f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR))
            }
            save(BlockScope(after, leave), PortId.ROOT_EXIT, flow(x),
                f.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
            val output = f.pattern(ret, tail = Tail.EXACT, mark = mark)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, PairedDemand(DemandEntry.Zero, DemandExit.Data(output)))
            }.build()
            val actor = f.core(index = 5, L = 4, demand = demand)
            f.submitRestricted(actor, Reach.NORMAL)
            f.drain(actor)
            assertTrue(actor.summaries.all().any { (p, c) -> p.isZero && c.layer == Layer.NORMAL &&
                f.ops.leaves(c).any { it == output } },
                "The own-ZERO source must pass the extra gate and reach saved shrinking repeats; opposite=$opposite")
            assertTrue(f.processed.none { it.node.location.index in 1..4 },
                "No local current demand is needed for this saved-only component route")
        }
    }

    @Test fun `same-direction saved own ZERO source bypasses the runtime growth gate`() = savedSource(false)
    @Test fun `opposite saved effective ZERO source bypasses the runtime growth gate`() = savedSource(true)
}
