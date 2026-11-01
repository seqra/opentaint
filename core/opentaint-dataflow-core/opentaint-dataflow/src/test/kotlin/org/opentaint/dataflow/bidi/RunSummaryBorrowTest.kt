package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import kotlin.test.*

class RunSummaryBorrowTest {
    @Test fun `admitted borrowing sees the current T2 annotation replacement`() {
        val f = StoreFixtures()
        val summaries = RunSummaryStore(f.manager)
        val initial = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
        val flow = f.ops.startFact(initial) as FlowTree
        fun excluding(mark: TaintMark) = f.manager.flowTree(flow.base, flow.layer, flow.exclusion,
            MarkExclusions.of(f.manager.marks, mark), flow.root, flow.tail)
        assertTrue(summaries.borrow(initial).none())
        val first = excluding(f.mark("T"))
        assertNotNull(summaries.addAdmitted(initial, first))
        assertEquals(first.markExclusion, assertIs<FlowTree>(summaries.borrow(initial).single()).markExclusion)
        assertNotNull(summaries.addAdmitted(initial, excluding(f.mark("U"))))
        assertTrue(assertIs<FlowTree>(summaries.borrow(initial).single()).markExclusion.isEmpty)
        assertNull(summaries.addAdmitted(initial, first))
        assertEquals(1, summaries.borrow(initial).count())
    }

    @Test fun `borrow and outgoing view share admitted rows`() {
        val f = StoreFixtures()
        val summaries = RunSummaryStore(f.manager)
        val initial = f.manager.initial(f.pattern())
        val raw = f.fact()
        val guidance = f.fact(path = listOf(f.field("f")), layer = Layer.DEMAND)
        assertNotNull(summaries.addAdmitted(initial, raw))
        assertNotNull(summaries.addAdmitted(initial, guidance))
        assertEquals(setOf(raw, guidance), summaries.borrow(initial).toSet())
        assertEquals(listOf(guidance), summaries.demandEdges(Direction.FORWARD).map { it.second }.toList())
    }
}
