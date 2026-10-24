package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import kotlin.test.*

class FlowBackedOwnersTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val v = StoreValues(fixture)

    @Test
    fun `mixed exact protection stays in fallback when diagonal ANY is compressed`(): Unit = with(v) {
        val key = premise(tail = Tail.STAR)
        val any = pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = y)) as TaintTree
        val exact = pack(leaf(p(f, h), Tail.EXACT, mt, Layer.DEMAND, base = y)) as TaintTree
        val other = pack(leaf(p(g), Tail.ANY, mu, Layer.DEMAND, base = y)) as TaintTree
        val root = m.taintAlg.mergeAdd(m.taintAlg.mergeAdd(any.root, exact.root), other.root)
        val mixed = m.taintTree(y, Layer.DEMAND, root, anyTail = Tail.ANY, nonSubsumable = exact.root)
        val store = RunSummaryStore(m, flowBacked = true)
        assertNotNull(store.add(key, mixed))
        assertEquals(setOf(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = y),
            leaf(p(f, h), Tail.EXACT, mt, Layer.DEMAND, base = y),
            leaf(p(g), Tail.ANY, mu, Layer.DEMAND, base = y)),
            store.borrow(key).flatMap { decoded(it).asSequence() }.toSet())
        assertEquals(setOf(leaf(p(f, h), Tail.EXACT, mt, Layer.DEMAND, base = y)),
            store.borrow(key).filterIsInstance<TaintTree>().mapNotNull { it.protectedPart() }
                .flatMap { decoded(it).asSequence() }.toSet())
        val flowKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        store.add(flowKey, pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y)))
        assertEquals(setOf(leaf(p(f, h), Tail.EXACT, mt, Layer.DEMAND, base = y),
            leaf(p(g), Tail.ANY, mu, Layer.DEMAND, base = y)),
            store.borrow(key).flatMap { decoded(it).asSequence() }.toSet())
        assertTrue(store.borrow(key).filterIsInstance<TaintTree>().any { it.nonSubsumable != null })
    }

    @Test
    fun `publication candidates normalize old marked rows after late FLOW and restore late flags`(): Unit = with(v) {
        val key = premise(tail = Tail.STAR)
        val flowKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val marked = pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = y)) as TaintTree
        val flow = pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y))
        val added = fixture.fact(tail = Tail.EXACT)
        val sub = Subscription(fixture.method, CallerRef(fixture.key("caller"), m.zero, Layer.NORMAL, fixture.inst(1)),
            Layer.NORMAL, added)
        val mode = ApMode(true, Direction.FORWARD, 1)
        val index = PublicationIndex(m, fixture.ops, flowBacked = true)
        assertEquals(1, index.addAll(listOf(Publication(key, marked))).size)
        assertEquals(setOf(key), index.candidates(sub, mode).map { it.first.premise }.toSet())
        assertEquals(1, index.addAll(listOf(Publication(flowKey, flow))).size)
        assertEquals(setOf(flowKey), index.candidates(sub, mode).map { it.first.premise }.toSet())
        val protected = marked.withProtection(marked.root)
        assertEquals(1, index.addAll(listOf(Publication(key, protected))).size)
        val late = index.candidates(sub, mode)
        assertEquals(setOf(flowKey, key), late.map { it.first.premise }.toSet())
        assertNotNull((late.single { it.first.premise === key }.first.conclusion as TaintTree).nonSubsumable)
        assertTrue(index.addAll(listOf(Publication(key, protected))).isEmpty())
    }

    @Test
    fun `a newer NORMAL FLOW proof compacts only the matching input geometry and eligible layer`(): Unit = with(v) {
        val key = premise(tail = Tail.STAR)
        val otherKey = premise(p(h), Tail.STAR)
        val flowKey = premise(tail = Tail.STAR, mark = MarkSlot.STAR)
        val markedNormal = m.taintTree(y, Layer.NORMAL,
            (pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND, base = y)) as TaintTree).root, anyTail = Tail.ANY)
        val markedDemand = markedNormal.withLayer(Layer.DEMAND)
        val store = RunSummaryStore(m, flowBacked = true)
        store.add(key, markedNormal)
        store.add(key, markedDemand)
        store.add(otherKey, markedDemand)
        store.add(flowKey, pack(leaf(p(), Tail.ANY, MarkSlot.STAR, Layer.DEMAND, base = y)))
        assertEquals(setOf(Layer.NORMAL), store.borrow(key).map { it.layer }.toSet())
        val normalFlow = m.flowTree(y, Layer.NORMAL, ExclusionSet.Empty, MarkSet.EMPTY,
            FlowAlgebra.LEAF_NODE, Tail.ANY)
        store.add(flowKey, normalFlow)
        assertTrue(store.borrow(key).none())
        assertTrue(store.borrow(otherKey).any())
    }
}
