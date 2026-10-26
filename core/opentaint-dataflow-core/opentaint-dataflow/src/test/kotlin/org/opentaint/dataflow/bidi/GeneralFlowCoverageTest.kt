package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.NeutralRelationBatch
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DiagonalRelations
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import kotlin.test.*

class GeneralFlowCoverageTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = fixture.mark("T")
    private val base = AccessPathBase.Argument(0)
    private val output = AccessPathBase.Return
    private fun initial(atom: TaintMark = t, tail: Tail = Tail.STAR, e: ExclusionSet = ExclusionSet.Empty) =
        m.initial(base, null, tail, e, MarkSlot.Concrete(atom))
    private fun marked(path: List<Int> = listOf(f), atom: TaintMark = t, tail: Tail = Tail.STAR,
                       e: ExclusionSet = ExclusionSet.Empty, layer: Layer = Layer.DEMAND): TaintTree =
        m.taintTree(output, layer, m.taintAlg.prepend(m, m.path(path),
            m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(atom)))), e, tail)
    private fun flow(path: List<Int> = listOf(f), tail: Tail = Tail.STAR,
                     e: ExclusionSet = ExclusionSet.Empty, excluded: MarkSet = MarkSet.EMPTY,
                     layer: Layer = Layer.NORMAL) = m.flowTree(output, layer, e, excluded,
        FlowAlgebra.prepend(m, m.path(path), FlowAlgebra.LEAF_NODE), tail)
    private fun paths(facts: Sequence<Facts>) = facts.flatMap { fixture.ops.leaves(it).map { l -> l.fact.path } }.toSet()

    @Test fun `STAR covers equal paths and subset exclusions but never a descendant binder`() {
        val facts = marked(e = ExclusionSet.of(g))
        assertNull(removeFlowCovered(m, initial(), facts, listOf(flow())))
        assertNotNull(removeFlowCovered(m, initial(), marked(), listOf(flow(e = ExclusionSet.of(g)))))
        assertNotNull(removeFlowCovered(m, initial(), marked(listOf(f, g)), listOf(flow())))
        assertNotNull(removeFlowCovered(m, initial(), marked(), listOf(flow(emptyList()))))
        assertNotNull(removeFlowCovered(m, initial(), marked(), listOf(flow(tail = Tail.ANY))))
        assertNotNull(removeFlowCovered(m, initial(), marked(), listOf(flow(excluded = m.markSetOf(t)))))
        assertNotNull(removeFlowCovered(m, initial(), marked(layer = Layer.NORMAL), listOf(flow(layer = Layer.DEMAND))))
    }

    @Test fun `STAR protection is exact path scoped and repeated annotations stop`() {
        val store = DiagonalRelations(m)
        val i = initial()
        val parent = marked()
        val child = marked(listOf(f, g))
        assertNotNull(store.add(i, parent))
        assertNotNull(store.add(i, child.withProtection(child.root)))
        assertNull(store.add(i, child.withProtection(child.root)))
        store.compact(checkNotNull(flowInitialForCoverage(m, i)), flow())
        assertEquals(setOf(listOf(f, g)), paths(store.borrow(i)))
        assertNull(store.add(i, child.withProtection(child.root)))
    }

    @Test fun `full and group atoms keep complete initial geometry in both arrival orders`() {
        val group = m.marks.runtimeAtom(t, MarkMode.GROUP)
        for (atom in listOf(t, group)) for (tail in listOf(Tail.STAR, Tail.ANY)) for (flowFirst in listOf(false, true)) {
            val inputE = if (tail == Tail.STAR) ExclusionSet.of(g) else ExclusionSet.Empty
            val i = initial(atom, tail, inputE)
            val counterpart = checkNotNull(flowInitialForCoverage(m, i))
            assertEquals(tail, counterpart.tail)
            assertEquals(inputE, counterpart.exclusion)
            val store = RunSummaryStore(m, flowBacked = true)
            if (flowFirst) store.add(counterpart, flow())
            store.add(i, marked(atom = atom))
            if (!flowFirst) store.add(counterpart, flow())
            assertTrue(store.borrow(i).none())
        }
    }

    @Test fun `STAR coverage preserves exact siblings cross atoms and exact protection coordinates`() {
        val u = fixture.mark("U")
        val plain = marked()
        val exact = m.taintAlg.prepend(m, m.path(listOf(f)),
            m.taintAlg.leafNode(m.taintLeaves(m.markSetOf(t), MarkSet.EMPTY)))
        val mixedRoot = m.taintAlg.mergeAdd(m.taintAlg.mergeAdd(plain.root, marked(atom = u).root), exact)
        val mixed = m.taintTree(output, Layer.DEMAND, mixedRoot, anyTail = Tail.STAR,
            nonSubsumable = exact)
        val rest = assertNotNull(removeFlowCovered(m, initial(), mixed, listOf(flow()), mixed.nonSubsumable))
        val leaves = fixture.ops.leaves(rest).map { it.fact }.toSet()
        assertEquals(setOf(PathFact(output, listOf(f), Tail.EXACT, MarkSlot.Concrete(t)),
            PathFact(output, listOf(f), Tail.STAR, MarkSlot.Concrete(u))), leaves)
    }

    @Test fun `STAR traversal uses a complete candidate and handles deep equal paths without recursion`() {
        val path = List(32768) { f }
        val facts = marked(path)
        assertNull(removeFlowCovered(m, initial(), facts, listOf(flow(path))))
        assertNotNull(removeFlowCovered(m, initial(), facts, listOf(
            flow(path, excluded = m.markSetOf(t)), flow(emptyList()))))
        fixture.cancellation.cancel()
        try {
            assertFailsWith<org.opentaint.dataflow.util.Cancellation.Cancelled> {
                removeFlowCovered(m, initial(), facts, listOf(flow(path)))
            }
        } finally { fixture.cancellation.activate() }
    }

    @Test fun `typed diagonal decode keeps group and full atoms on their own premise`() {
        val u = fixture.mark("U")
        val atoms = listOf(t, u, m.marks.runtimeAtom(t, MarkMode.GROUP))
        val e = ExclusionSet.of(g)
        val store = DiagonalRelations(m)
        val shape = checkNotNull(flowInitialForCoverage(m, initial(e = e)))
        val geometry = FlowAlgebra.prepend(m, m.path(listOf(f)), FlowAlgebra.LEAF_NODE)
        val packet = DiagonalDelta(shape, output, Layer.DEMAND, geometry, m.intern(MarkSet(atoms.map { it.id }.toIntArray())),
            protected = false, tail = Tail.STAR, exclusion = e)
        assertNotNull(store.addDiagonal(packet))
        assertEquals(1, store.rowCount)
        assertEquals(atoms.size, store.all().count())
        for ((premise, facts) in store.all()) {
            val atom = ((premise as InitialAp).mark as MarkSlot.Concrete).mark
            assertEquals(e, premise.exclusion)
            assertEquals(setOf(atom), fixture.ops.leaves(facts).map { (it.fact.mark as MarkSlot.Concrete).mark }.toSet())
            assertEquals(setOf(Tail.STAR), fixture.ops.leaves(facts).map { it.fact.tail }.toSet())
            assertEquals(e, (facts as TaintTree).exclusion)
        }
    }

    @Test fun `STAR packet stores output tail exclusions and independent original marks`() {
        val e = ExclusionSet.of(g)
        val i = initial(e = e)
        val shape = checkNotNull(flowInitialForCoverage(m, i))
        val value = marked(e = e)
        val packet = checkNotNull(NeutralRelationBatch.toDiagonal(m, shape, value, m.markSetOf(t)))
        assertEquals(Tail.STAR, packet.tail)
        assertEquals(e, packet.exclusion)
        val decoded = checkNotNull(NeutralRelationBatch.fromDiagonal(m, packet)).decode().single()
        assertSame(i, decoded.first)
        assertEquals(Tail.STAR, decoded.second.anyTail)
        assertEquals(e, decoded.second.exclusion)
        val store = DiagonalRelations(m)
        assertNotNull(store.addDiagonal(packet))
        assertEquals(emptyList(), store.addDiagonal(packet))
        val flagged = packet.copy(protected = true)
        assertEquals(listOf(flagged), store.addDiagonal(flagged))
        assertEquals(emptyList(), store.addDiagonal(flagged))
    }
}
