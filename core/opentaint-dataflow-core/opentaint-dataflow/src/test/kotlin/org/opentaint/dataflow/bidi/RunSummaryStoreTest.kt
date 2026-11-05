package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class RunSummaryStoreTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val v = StoreValues(fixture)

    @Test fun `admitted store enforces K6 and multi-premise TAINT`(): Unit = with(v) {
        val concrete = premise()
        val abstract = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val multiple = nd()
        val taint = pack(leaf(p(f)))
        val flow = pack(flow(p(f)))
        for ((key, value) in listOf(concrete to flow, abstract to taint, abstract to Reach.NORMAL,
            multiple to flow, multiple to Reach.NORMAL, multiple to Reach.DEMAND)) {
            val store = RunSummaryStore(m)
            assertFails { store.addAdmitted(key, value) }
            assertTrue(store.all().none())
            assertTrue(store.demandEdges(Direction.FORWARD).none())
        }
        val store = RunSummaryStore(m)
        for ((key, value) in listOf(concrete to taint, abstract to flow, multiple to taint)) {
            assertNotNull(store.addAdmitted(key, value))
            assertNull(store.addAdmitted(key, value))
        }
    }

    @Test fun `final headers select outgoing view without a second collection`(): Unit = with(v) {
        val keys = listOf(premise(), premise(tail = Tail.ANY_TAINT, e = ex(g)), nd(), m.zero)
        for (key in keys) for (layer in Layer.entries) for (direction in Direction.entries)
            for (backed in listOf(false, true)) {
                val store = RunSummaryStore(m, flowBacked = backed)
                val leaves = setOf(leaf(p(f), layer = layer), leaf(p(g), mark = mu, layer = layer))
                store.addAdmitted(key, pack(*leaves.toTypedArray()))
                val rows = leaves.map { key to it }.toSet()
                val selected = layer == Layer.DEMAND || key is PremiseSet ||
                    (direction == Direction.BACKWARD && key.isZero)
                assertEquals(rows, observed(store.all()))
                assertEquals(if (selected) rows else emptySet(), observed(store.demandEdges(direction)))
                assertEquals(if (selected) store.census() else org.opentaint.dataflow.bidi.store.RelationCensus.ZERO,
                    store.demandCensus(direction))
            }
    }

    @Test fun `REACH and premise tail exclusion keys remain independent`(): Unit = with(v) {
        val keys = listOf(m.zero, premise(), premise(tail = Tail.ANY), premise(tail = Tail.ANY_TAINT),
            premise(tail = Tail.ANY_TAINT, e = ex(g)), premise(tail = Tail.ANY_TAINT, e = ex(h)))
        val store = RunSummaryStore(m)
        for (key in keys) for (layer in Layer.entries) {
            assertSame(Reach.of(layer), store.addAdmitted(key, Reach.of(layer)))
            assertNull(store.addAdmitted(key, Reach.of(layer)))
        }
        val expected: Set<Pair<PremiseKey, Facts>> = keys.flatMap { key ->
            Layer.entries.map { key to (Reach.of(it) as Facts) }
        }.toSet()
        assertEquals(expected, store.all().toSet())
        for (direction in Direction.entries) assertEquals(expected.filter { (key, facts) ->
            facts.layer == Layer.DEMAND || direction == Direction.BACKWARD && key.isZero
        }.toSet(), store.demandEdges(direction).toSet())
    }

    @Test fun `T1 returns fresh deltas in either insertion order`(): Unit = with(v) {
        val cases = listOf(
            Triple(premise(), listOf(leaf(p(f)), leaf(p(g), mark = mu)), listOf(leaf(p(f)), leaf(p(g)))),
            Triple(premise(tail = Tail.STAR, mark = MarkSlot.STAR), listOf(flow(p(f))), listOf(flow(p(f)), flow(p(g)))),
        )
        for ((key, left, right) in cases) for (order in listOf(listOf(left, right), listOf(right, left))) {
            val store = RunSummaryStore(m)
            fun add(leaves: List<Conclusion>) = store.addAdmitted(key, pack(*leaves.toTypedArray()))
            assertEquals(order[0].toSet(), decoded(assertNotNull(add(order[0]))))
            val expected = order[1].toSet() - order[0].toSet()
            val delta = add(order[1])
            if (expected.isEmpty()) assertNull(delta) else assertEquals(expected, decoded(assertNotNull(delta)))
            assertEquals((left + right).map { key to it }.toSet(), observed(store.all()))
            assertNull(add(left)); assertNull(add(right))
        }
    }

    @Test fun `T2 annotation union preserves the current delta`(): Unit = with(v) {
        data class Case(val key: PremiseKey, val left: List<Conclusion>, val right: List<Conclusion>, val merged: Set<Conclusion>)
        val flowKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val exact = leaf(p(h), mark = mu)
        val cases = listOf(
            Case(flowKey, listOf(flow(p(), e = ex(f, h))), listOf(flow(p(), e = ex(g, h))), setOf(flow(p(), e = ex(h)))),
            Case(flowKey, listOf(flow(p(), e = ex(h), mx = marks(t.id))), listOf(flow(p(), e = ex(h), mx = marks(u.id))),
                setOf(flow(p(), e = ex(h)))),
            Case(premise(), listOf(leaf(p(), Tail.ANY_TAINT, e = ex(f)), exact),
                listOf(leaf(p(), Tail.ANY_TAINT, e = ex(g)), exact), setOf(leaf(p(), Tail.ANY_TAINT), exact)),
        )
        for (case in cases) for (order in listOf(listOf(case.left, case.right), listOf(case.right, case.left))) {
            val store = RunSummaryStore(m)
            fun add(leaves: List<Conclusion>) = store.addAdmitted(case.key, pack(*leaves.toTypedArray()))
            add(order[0])
            assertEquals(case.merged, decoded(assertNotNull(add(order[1]))))
            assertEquals(case.merged.map { case.key to it }.toSet(), observed(store.all()))
            assertNull(add(case.left)); assertNull(add(case.right))
        }
    }

    @Test fun `covered offers add no delta and MAY removes exact support only in its own layer`(): Unit = with(v) {
        val key = premise()
        val general = leaf(p(f), Tail.ANY, layer = Layer.DEMAND)
        val specific = leaf(p(f, g), layer = Layer.DEMAND)
        val normal = leaf(p(f, g))
        for (broadFirst in listOf(false, true)) {
            val store = RunSummaryStore(m)
            if (!broadFirst) assertNotNull(store.addAdmitted(key, pack(specific)))
            assertNotNull(store.addAdmitted(key, pack(general)))
            assertNull(store.addAdmitted(key, pack(specific)))
            assertNotNull(store.addAdmitted(key, pack(normal)))
            val demand = setOf(general)
            assertEquals((demand + normal).map { key to it }.toSet(), observed(store.all()))
            assertEquals(demand.map { key to it }.toSet(), observed(store.demandEdges(Direction.FORWARD)))
        }
        val store = RunSummaryStore(m)
        val must = leaf(p(f), Tail.ANY_TAINT, e = ex(h))
        store.addAdmitted(key, pack(must))
        assertNull(store.addAdmitted(key, pack(leaf(p(f, g), Tail.ANY_TAINT, e = ex(h)))))
        assertNotNull(store.addAdmitted(key, pack(normal)))
        assertNotNull(store.addAdmitted(premise(tail = Tail.ANY_TAINT, e = ex(g)), pack(must)))
    }

    @Test fun `deep admitted rows survive cache loss in both lanes`(): Unit = with(v) {
        val path = List(32768) { f }
        val normal = leaf(path, Tail.ANY_TAINT, e = ex(h))
        val demand = leaf(path, Tail.ANY, layer = Layer.DEMAND)
        val key = nd()
        val store = RunSummaryStore(m)
        assertEquals(setOf(normal), decoded(assertNotNull(store.addAdmitted(key, pack(normal)))))
        assertEquals(setOf(demand), decoded(assertNotNull(store.addAdmitted(key, pack(demand)))))
        m.softRefs.cleanup(); m.softRefs.enable()
        assertNull(store.addAdmitted(key, pack(normal))); assertNull(store.addAdmitted(key, pack(demand)))
        assertEquals(setOf(key to normal, key to demand), observed(store.all()))
        assertEquals(observed(store.all()), observed(store.demandEdges(Direction.FORWARD)))
    }

    @Test fun `cancelled mutation and views do not change admitted state`(): Unit = with(v) {
        val key = premise()
        val first = leaf(p(f))
        val piece = leaf(p(g), layer = Layer.DEMAND)
        val store = RunSummaryStore(m)
        store.addAdmitted(key, pack(first)); store.addAdmitted(key, pack(piece))
        fixture.cancellation.cancel()
        try {
            assertFailsWith<Cancellation.Cancelled> { store.addAdmitted(key, pack(leaf(p(h)))) }
            assertFailsWith<Cancellation.Cancelled> { store.all().toList() }
            assertFailsWith<Cancellation.Cancelled> { store.demandEdges(Direction.FORWARD).toList() }
        } finally { fixture.cancellation.activate() }
        assertEquals(setOf(key to first, key to piece), observed(store.all()))
        assertEquals(setOf(key to piece), observed(store.demandEdges(Direction.FORWARD)))
    }
}
