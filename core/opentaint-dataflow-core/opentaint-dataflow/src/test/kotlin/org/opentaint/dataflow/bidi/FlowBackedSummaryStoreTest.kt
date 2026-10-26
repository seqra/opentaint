package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import kotlin.test.*

class FlowBackedSummaryStoreTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)
    private val m = fixture.manager

    @Test fun `covered marked outputs are removed in both arrival orders from raw and demand`(): Unit = with(v) {
        val markedInitial = premise(tail = Tail.STAR)
        val flowInitial = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val marked = pack(leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y))
        val flow = pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y))
        for (flowFirst in listOf(false, true)) {
            val store = RunSummaryStore(m, flowBacked = true)
            for ((initial, facts) in if (flowFirst) listOf(flowInitial to flow, markedInitial to marked)
                else listOf(markedInitial to marked, flowInitial to flow)) {
                store.add(initial, facts)
                store.addDemand(initial, facts)
            }
            assertEquals(listOf(flowInitial to flow), store.all().toList())
            assertEquals(listOf(flowInitial to flow), store.demandEdges().toList())
            assertTrue(store.borrow(markedInitial).none())
        }
    }

    @Test fun `late protection restores marked guidance after plain coverage`(): Unit = with(v) {
        val markedInitial = premise(tail = Tail.STAR)
        val flowInitial = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val marked = pack(leaf(p(f), Tail.ANY, layer = Layer.DEMAND, base = y)) as TaintTree
        val flow = pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y))
        val store = RunSummaryStore(m, flowBacked = true)
        store.add(flowInitial, flow)
        assertNull(store.add(markedInitial, marked))
        val restored = assertNotNull(store.add(markedInitial, marked.withProtection(marked.root))) as TaintTree
        assertNotNull(restored.nonSubsumable)
        assertEquals(2, store.all().count())
        assertNull(store.add(markedInitial, marked.withProtection(marked.root)))
    }

    @Test fun `partial output and cross mark relations keep their guidance`(): Unit = with(v) {
        val markedInitial = premise(tail = Tail.STAR)
        val flowInitial = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val marked = pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = y),
            leaf(p(g), Tail.ANY, mt, Layer.DEMAND, base = y),
            leaf(p(f), Tail.ANY, mu, Layer.DEMAND, base = y))
        val flow = pack(leaf(p(f), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y))
        val store = RunSummaryStore(m, flowBacked = true)
        store.add(flowInitial, flow)
        val delta = assertNotNull(store.add(markedInitial, marked))
        assertEquals(setOf(leaf(p(g), Tail.ANY, mt, Layer.DEMAND, base = y),
            leaf(p(f), Tail.ANY, mu, Layer.DEMAND, base = y)), decoded(delta))
    }

    @Test fun `same base identity is subsumed while unsupported tails keep exact fallback`(): Unit = with(v) {
        val initial = premise(tail = Tail.STAR)
        val flowInitial = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val store = RunSummaryStore(m, flowBacked = true)
        store.add(flowInitial, pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND)))
        val sameBase = pack(leaf(p(), Tail.ANY, layer = Layer.DEMAND))
        assertNull(store.add(initial, sameBase))
        val exact = pack(leaf(p(), Tail.EXACT, layer = Layer.DEMAND, base = y))
        store.add(flowInitial, pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y)))
        assertNotNull(store.add(initial, exact))
    }
}
