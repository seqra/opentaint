package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DiagonalRelations
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import kotlin.test.*

class FlowBackedSameBaseTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val base = AccessPathBase.Argument(0)
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val t = fixture.mark("T")
    private fun initial(path: List<Int> = emptyList(), mark: MarkSlot = MarkSlot.Concrete(t)) =
        m.initial(base, m.path(path), Tail.STAR, ExclusionSet.Empty, mark)
    private fun flow(paths: List<List<Int>> = listOf(emptyList())): FlowTree = m.flowTree(base, Layer.DEMAND,
        ExclusionSet.Empty, MarkSet.EMPTY, paths.map { FlowAlgebra.prepend(m, m.path(it), FlowAlgebra.LEAF_NODE) }
            .reduce { a, b -> FlowAlgebra.mergeAdd(a, b) }, Tail.ANY)
    private fun marked(paths: List<List<Int>>): TaintTree = m.taintTree(base, Layer.DEMAND,
        paths.map { m.taintAlg.prepend(m, m.path(it), m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(t)))) }
            .reduce { a, b -> m.taintAlg.mergeAdd(a, b) }, anyTail = Tail.ANY)
    private fun paths(values: Sequence<Facts>): Set<List<Int>> =
        values.flatMap { fixture.ops.leaves(it).map { leaf -> leaf.fact.path } }.toSet()

    @Test
    fun `same base child is an effect for both FLOW ANY and diagonal TAINT ANY`() {
        val marked = initial().toPattern().fact
        val flow = initial(mark = MarkSlot.STAR).toPattern().fact
        val markedChild = PathFact(base, listOf(f), Tail.ANY, MarkSlot.Concrete(t))
        val flowPrefix = PathFact(base, emptyList(), Tail.ANY, MarkSlot.STAR)
        assertFalse(hasNoMemoryEffect(marked, markedChild))
        assertFalse(hasNoMemoryEffect(flow, flowPrefix))
        assertTrue(hasNoMemoryEffect(marked, markedChild.copy(path = emptyList())))
    }

    @Test
    fun `same base identity and child are both removed in both orders`() {
        val concrete = initial()
        val abstract = initial(mark = MarkSlot.STAR)
        val taint = marked(listOf(emptyList(), listOf(f)))
        val cover = flow()
        for (flowFirst in listOf(false, true)) {
            val store = RunSummaryStore(m, flowBacked = true)
            val offers = if (flowFirst) listOf(abstract to cover, concrete to taint)
                else listOf(concrete to taint, abstract to cover)
            for ((key, value) in offers) {
                store.add(key, value)
                store.addDemand(key, value)
            }
            assertTrue(store.borrow(concrete).none())
            assertTrue(store.demandEdges().none { it.first === concrete })
            assertTrue(store.all().any { it.first === abstract && it.second is FlowTree })
        }
    }

    @Test
    fun `same base nonidentity paths are removed without restoring structural branch nodes`() {
        val concrete = initial(listOf(f))
        val abstract = initial(listOf(f), MarkSlot.STAR)
        val taint = marked(listOf(listOf(f, g), listOf(h)))
        for (flowFirst in listOf(false, true)) {
            val store = RunSummaryStore(m, flowBacked = true)
            if (flowFirst) store.add(abstract, flow())
            store.add(concrete, taint)
            if (!flowFirst) store.add(abstract, flow())
            assertTrue(store.borrow(concrete).none())
        }
    }

    @Test
    fun `packed same base compaction removes identity and effect outputs`() {
        val concrete = initial(listOf(f))
        val abstract = initial(listOf(f), MarkSlot.STAR)
        val store = DiagonalRelations(m)
        store.add(concrete, marked(listOf(listOf(f), listOf(f, g), listOf(h))))
        store.compact(abstract, flow())
        assertTrue(store.borrow(concrete).none())
        val before = store.census()
        store.compact(abstract, flow())
        assertEquals(before, store.census(), "Repeated compaction is not new marked work")
    }

    @Test
    fun `prefix coverage preserves same path and unrelated output siblings`() {
        val concrete = initial()
        val abstract = initial(mark = MarkSlot.STAR)
        val taint = marked(listOf(emptyList(), listOf(f, h), listOf(g)))
        for (flowFirst in listOf(false, true)) {
            val store = RunSummaryStore(m, flowBacked = true)
            if (flowFirst) store.add(abstract, flow(listOf(listOf(f))))
            store.add(concrete, taint)
            if (!flowFirst) store.add(abstract, flow(listOf(listOf(f))))
            assertEquals(setOf(emptyList(), listOf(g)), paths(store.borrow(concrete)))
        }
    }

    @Test
    fun `same base exact and protected nonidentity outputs keep marked guidance`() {
        val concrete = initial()
        val abstract = initial(mark = MarkSlot.STAR)
        val store = RunSummaryStore(m, flowBacked = true)
        store.add(abstract, flow())
        val exact = m.factsOf(PathFact(base, listOf(f), Tail.EXACT, MarkSlot.Concrete(t)),
            ExclusionSet.Empty, Layer.DEMAND)
        assertNotNull(store.add(concrete, exact))
        val protected = marked(listOf(listOf(g))).let { it.withProtection(it.root) }
        assertNotNull(store.add(concrete, protected))
        assertEquals(setOf(listOf(f), listOf(g)), paths(store.borrow(concrete)))
        assertTrue(store.borrow(concrete).filterIsInstance<TaintTree>().any { it.nonSubsumable != null })
    }
}
