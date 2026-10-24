package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DiagonalRelations
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class DiagonalRelationsTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val input = AccessPathBase.Argument(0)
    private val output = AccessPathBase.Return

    private fun initial(mark: TaintMark = t, path: List<Int> = emptyList()) =
        m.initial(input, m.path(path), Tail.STAR, ExclusionSet.Empty, MarkSlot.Concrete(mark))
    private fun facts(mark: TaintMark = t, paths: List<List<Int>> = listOf(listOf(f)),
                      layer: Layer = Layer.DEMAND): TaintTree {
        val root = paths.map { m.taintAlg.prepend(m, m.path(it),
            m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(mark)))) }
            .reduce { a, b -> m.taintAlg.mergeAdd(a, b) }
        return m.taintTree(output, layer, root, anyTail = Tail.ANY)
    }
    private fun flow(paths: List<List<Int>>, excluded: MarkSet = MarkSet.EMPTY,
                     layer: Layer = Layer.DEMAND): FlowTree = m.flowTree(output, layer, ExclusionSet.Empty,
        excluded, paths.map { FlowAlgebra.prepend(m, m.path(it), FlowAlgebra.LEAF_NODE) }
            .reduce { a, b -> FlowAlgebra.mergeAdd(a, b) }, Tail.ANY)
    private fun paths(facts: Facts): Set<List<Int>> = fixture.ops.leaves(facts).map { it.fact.path }.toSet()
    private fun stored(store: DiagonalRelations, key: InitialAp): Set<List<Int>> =
        store.borrow(key).flatMap { fixture.ops.leaves(it).map { leaf -> leaf.fact.path } }.toSet()
    private fun flags(facts: Facts): Set<List<Int>> = (facts as TaintTree).protectedPart()?.let(::paths) ?: emptySet()

    @Test
    fun `equal geometry shares one exact mark mask and decodes without cross products`() {
        val store = DiagonalRelations(m)
        for (mark in listOf(t, u)) {
            assertTrue(store.supports(initial(mark), facts(mark)))
            assertNotNull(store.add(initial(mark), facts(mark)))
            assertNull(store.add(initial(mark), facts(mark)))
        }
        assertEquals(1, store.rowCount)
        assertEquals(2, store.markMembershipCount)
        val decoded = store.all().toList()
        assertEquals(2, decoded.size)
        for ((key, value) in decoded) {
            val mark = ((key as InitialAp).mark as MarkSlot.Concrete).mark
            assertEquals(setOf(mark), fixture.ops.leaves(value).map { (it.fact.mark as MarkSlot.Concrete).mark }.toSet())
            assertEquals(Layer.DEMAND, value.layer)
            assertEquals(setOf(Tail.ANY), fixture.ops.leaves(value).map { it.fact.tail }.toSet())
            assertEquals(setOf(listOf(f)), paths(value))
        }
    }

    @Test
    fun `admission subtracts old geometry before constructing a scalar delta`() {
        val store = DiagonalRelations(m)
        store.add(initial(), facts(paths = listOf(listOf(f))))
        val delta = assertNotNull(store.add(initial(), facts(paths = listOf(listOf(f), listOf(g)))))
        assertEquals(setOf(listOf(g)), paths(delta))
        assertEquals(setOf(listOf(f), listOf(g)), stored(store, initial()))
        assertNull(store.add(initial(), facts(paths = listOf(listOf(f, h)))))
        assertEquals(2, store.markMembershipCount)
    }

    @Test
    fun `partial protection splits geometry and protection-only growth is emitted once`() {
        val store = DiagonalRelations(m)
        val both = facts(paths = listOf(listOf(f), listOf(g)))
        store.add(initial(), both)
        val protected = both.withProtection(facts(paths = listOf(listOf(f))).root)
        val delta = assertNotNull(store.add(initial(), protected))
        assertEquals(setOf(listOf(f)), paths(delta))
        assertEquals(setOf(listOf(f)), flags(delta))
        assertNull(store.add(initial(), protected))
        val rows = store.borrow(initial()).toList()
        assertEquals(2, rows.size)
        assertEquals(setOf(listOf(f)), rows.flatMap { flags(it) }.toSet())
        assertEquals(setOf(listOf(f), listOf(g)), stored(store, initial()))
        store.compact(checkNotNull(flowInitialForCoverage(m, initial())), flow(listOf(emptyList())))
        assertEquals(setOf(listOf(f)), stored(store, initial()))
        assertEquals(1, store.rowCount)
    }

    @Test
    fun `a narrower protected ANY offer upgrades its existing containing leaf only`() {
        val store = DiagonalRelations(m)
        store.add(initial(), facts(paths = listOf(listOf(f), listOf(g))))
        val child = facts(paths = listOf(listOf(f, h)))
        val delta = assertNotNull(store.add(initial(), child.withProtection(child.root)))
        assertEquals(setOf(listOf(f)), paths(delta))
        assertEquals(setOf(listOf(f)), flags(delta))
        assertNull(store.add(initial(), child.withProtection(child.root)))
        assertEquals(setOf(listOf(f)), store.borrow(initial()).flatMap { flags(it).asSequence() }.toSet())
    }

    @Test
    fun `compaction shares geometry work and preserves excluded and protected marks`() {
        val store = DiagonalRelations(m)
        for (mark in listOf(t, u)) store.add(initial(mark), facts(mark, listOf(listOf(f), listOf(g))))
        store.compact(checkNotNull(flowInitialForCoverage(m, initial())), flow(listOf(listOf(f)), MarkSet.of(u)))
        assertEquals(setOf(listOf(g)), stored(store, initial(t)))
        assertEquals(setOf(listOf(f), listOf(g)), stored(store, initial(u)))
        val protected = facts(t, listOf(listOf(f))).let { it.withProtection(it.root) }
        assertNotNull(store.add(initial(t), protected))
        store.compact(checkNotNull(flowInitialForCoverage(m, initial())), flow(listOf(emptyList())))
        assertEquals(setOf(listOf(f)), stored(store, initial(t)))
        assertTrue(store.borrow(initial(u)).none())
        assertEquals(1, store.rowCount)
        assertEquals(1, store.markMembershipCount)
    }

    @Test
    fun `layers initial shapes and unsupported mixed marks never merge`() {
        val store = DiagonalRelations(m)
        val base = facts()
        assertFalse(store.supports(initial(), Reach.DEMAND))
        assertFalse(store.supports(initial(), fixture.fact(base = output)))
        assertFalse(store.supports(initial(), facts(u)))
        assertFalse(store.supports(initial(), m.taintTree(output, Layer.DEMAND,
            m.taintAlg.mergeAdd(base.root, facts(u).root), anyTail = Tail.ANY)))
        val exact = m.factsOf(PathFact(output, listOf(f), Tail.EXACT, MarkSlot.Concrete(t)), ExclusionSet.Empty, Layer.DEMAND)
        assertFalse(store.supports(initial(), exact))
        assertFalse(store.supports(m.initial(input, null, Tail.EXACT, ExclusionSet.Empty, MarkSlot.Concrete(t)), base))
        store.add(initial(), base)
        store.add(initial(), facts(layer = Layer.NORMAL))
        store.add(initial(path = listOf(h)), base)
        assertEquals(3, store.rowCount)
        store.compact(checkNotNull(flowInitialForCoverage(m, initial())), flow(listOf(emptyList())))
        assertEquals(setOf(Layer.NORMAL), store.borrow(initial()).map { it.layer }.toSet())
        assertEquals(setOf(listOf(f)), stored(store, initial(path = listOf(h))))
    }

    @Test
    fun `compact exact decoder and late FLOW are independent of input order`() {
        for (reverse in listOf(false, true)) {
            val store = DiagonalRelations(m)
            val ordered = listOf(t, u).let { if (reverse) it.reversed() else it }
            for (mark in ordered) store.add(initial(mark), facts(mark, listOf(listOf(f, h), listOf(g))))
            store.compact(checkNotNull(flowInitialForCoverage(m, initial())), flow(listOf(listOf(f))))
            for (mark in ordered) assertEquals(setOf(listOf(g)), stored(store, initial(mark)))
            assertEquals(1, store.rowCount)
            assertEquals(2, store.markMembershipCount)
        }
    }

    @Test
    fun `deep exact codec and cancellation keep the store usable`() {
        val path = List(32768) { f }
        val store = DiagonalRelations(m)
        store.add(initial(), facts(paths = listOf(path)))
        assertEquals(setOf(path), stored(store, initial()))
        fixture.cancellation.cancel()
        try {
            assertFailsWith<Cancellation.Cancelled> { store.add(initial(), facts()) }
            assertFailsWith<Cancellation.Cancelled> { store.all().toList() }
            assertFailsWith<Cancellation.Cancelled> { store.borrow(initial()).toList() }
        } finally { fixture.cancellation.activate() }
        assertEquals(setOf(path), stored(store, initial()))
        store.compact(checkNotNull(flowInitialForCoverage(m, initial())), flow(listOf(emptyList())))
        assertTrue(store.isEmpty)
    }
}
