package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.Direction
import org.opentaint.dataflow.bidi.ap.Reach
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.DemandEntry
import org.opentaint.dataflow.bidi.store.DemandExit
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.PairedDemand
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class LoopBlockEmptyReverseJoinTest {
    @Test fun `both real reverse predecessors cross an empty prefix without physical work in it`() {
        // while (first()) {
        //   if (repeat()) continue;
        //   if (left()) break;  // physical tail 3 -> second header 5
        //   else break;        // physical tail 4 -> second header 5
        // }
        // while (second()) { continue; }
        // return;
        // The two loops are successive: BL2 is empty. In reverse, the shared
        // first-loop normal join expands to both true predecessors, 3 and 4.
        MethodAnalysisFixtures(successors = listOf(
            listOf(1),        // 0 original entry
            listOf(2, 3, 4),  // 1 first-loop header
            listOf(1),        // 2 first-loop repeat
            listOf(5),        // 3 first normal leave tail
            listOf(5),        // 4 second normal leave tail
            listOf(6, 7),     // 5 second-loop header
            listOf(5),        // 6 second-loop repeat
            listOf(8),        // 7 suffix
            emptyList(),      // 8 normal exit
            emptyList(),      // 9 unused exceptional exit
        ), normalExit = 8, exceptionalExit = 9).use { f ->
            val layout = f.contexts.blockLayout(f.key)
            val body = layout[layout.root]
            val first = layout[checkNotNull(body.loop)]
            val afterFirst = layout[checkNotNull(body.after)]
            val emptyPrefix = checkNotNull(afterFirst.before)
            val second = layout[checkNotNull(afterFirst.loop)]
            val suffix = checkNotNull(afterFirst.after)
            val firstNormal = layout.normalExits.single { it.loop == first.id }
            val secondNormal = layout.normalExits.single { it.loop == second.id }.id
            val firstInput = checkNotNull(layout.port(0, 1)).id
            assertTrue(layout[emptyPrefix].instructions.isEmpty())
            assertEquals(setOf(3 to 5, 4 to 5), firstNormal.routes.map { port ->
                val edge = layout.ports[port.ordinal]
                edge.from to edge.to
            }.toSet())
            val control = PairedDemand(DemandEntry.Target, DemandExit.Zero)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, control)
                add(f.key, BlockScope(afterFirst.id, PortId.ROOT_EXIT), firstNormal.id, control)
                add(f.key, BlockScope(suffix, PortId.ROOT_EXIT), secondNormal, control)
                add(f.key, BlockScope(second.id, secondNormal), firstNormal.id, control)
                add(f.key, BlockScope(emptyPrefix, firstNormal.id), firstNormal.id, control)
                add(f.key, BlockScope(first.id, firstNormal.id), firstInput, control)
                add(f.key, BlockScope(checkNotNull(body.before), firstInput), PortId.ROOT_ENTRY, control)
            }.build()
            val actor = f.core(index = 2, L = 1, demand = demand)
            assertEquals(Direction.BACKWARD, actor.config.direction)
            actor.addRootZero()
            f.drain(actor, quantum = 1)

            val runtime = assertNotNull(actor.blockRuntime)
            val empty = runtime.state(BlockScope(emptyPrefix, firstNormal.id))
            assertEquals(listOf(f.manager.zero), empty.initials.all().toList())
            assertEquals(0L, empty.steps, "An empty prefix never executes a physical predecessor")
            assertTrue(empty.portSummaries.entries().any { (exit, rows) ->
                exit == firstNormal.id && rows.all().any { (initial, result) ->
                    initial.isZero && result is Reach
                }
            }, "The already admitted ZERO also takes the existing empty identity on a late second target")
            for (predecessor in listOf(3, 4)) assertTrue(f.processed.any { it.node.location.index == predecessor },
                "Reverse canonical delivery must retain actual predecessor $predecessor in its owning first loop")
            runtime.requireIdle()
            actor.freeze()
        }
    }
}
