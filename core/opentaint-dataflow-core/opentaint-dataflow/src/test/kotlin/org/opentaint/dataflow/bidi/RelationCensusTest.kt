package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DiagonalRelations
import org.opentaint.dataflow.bidi.store.RelationCensus
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class RelationCensusTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val input = AccessPathBase.Argument(0)
    private val output = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private fun initial(mark: MarkSlot = MarkSlot.Concrete(t)) =
        m.initial(input, null, Tail.STAR, ExclusionSet.Empty, mark)
    private fun any(mark: TaintMark, path: List<Int> = listOf(f)): TaintTree =
        m.factsOf(PathFact(output, path, Tail.ANY, MarkSlot.Concrete(mark)), ExclusionSet.Empty, Layer.DEMAND) as TaintTree

    @Test
    fun `diagonal census multiplies masks by path occurrences in a shared DAG`() {
        val store = DiagonalRelations(m)
        for (mark in listOf(t, u)) {
            val leaf = m.taintAlg.leafNode(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(mark)))
            val root = m.taintAlg.node(TaintLeaves.EMPTY, intArrayOf(f, g).sortedArray(), arrayOf(leaf, leaf))
            val facts = m.taintTree(output, Layer.DEMAND, root, anyTail = Tail.ANY)
            store.add(initial(MarkSlot.Concrete(mark)), if (mark == t) facts.withProtection(root) else facts)
        }
        assertEquals(RelationCensus(concreteOutputMemberships = 4, protectedOutputMemberships = 2,
            diagonalGeometryRows = 1, diagonalMarkRows = 2), store.census())
        val flow = m.flowTree(output, Layer.DEMAND, ExclusionSet.Empty, MarkSet.EMPTY,
            FlowAlgebra.prepend(m, m.path(listOf(f)), FlowAlgebra.LEAF_NODE), Tail.ANY)
        store.compact(initial(MarkSlot.STAR), flow)
        assertEquals(RelationCensus(concreteOutputMemberships = 3, protectedOutputMemberships = 2,
            diagonalGeometryRows = 2, diagonalMarkRows = 2), store.census())
    }

    @Test
    fun `scalar mixed roots count exact and ANY marks with shared subtree multiplicity`() {
        val rootLeaf = m.taintLeaves(m.markSetOf(t), m.markSetOf(u))
        val sharedLeaf = m.taintAlg.leafNode(m.taintLeaves(m.intern(m.markSetOf(t) + u), m.markSetOf(t)))
        val root = m.taintAlg.node(rootLeaf, intArrayOf(f, g).sortedArray(), arrayOf(sharedLeaf, sharedLeaf))
        val protected = m.taintAlg.node(m.taintLeaves(MarkSet.EMPTY, m.markSetOf(u)), intArrayOf(f),
            arrayOf(m.taintAlg.leafNode(m.taintLeaves(m.markSetOf(t), MarkSet.EMPTY))))
        val facts = m.taintTree(output, Layer.DEMAND, root, anyTail = Tail.ANY, nonSubsumable = protected)
        val store = RunSummaryStore(m)
        store.add(initial(), facts)
        val flowLeaf = FlowAlgebra.LEAF_NODE
        val flowRoot = FlowAlgebra.node(FlowLeaf.NONE, intArrayOf(f, g).sortedArray(), arrayOf(flowLeaf, flowLeaf))
        store.add(initial(MarkSlot.STAR), m.flowTree(output, Layer.DEMAND, ExclusionSet.Empty, MarkSet.EMPTY, flowRoot, Tail.ANY))
        store.add(m.zero, Reach.NORMAL)
        store.addDemand(initial(), any(u))
        assertEquals(RelationCensus(concreteOutputMemberships = 8, protectedOutputMemberships = 2,
            scalarConcreteRows = 1, flowOutputAnnotations = 2), store.census())
        assertEquals(RelationCensus(concreteOutputMemberships = 1, scalarConcreteRows = 1), store.demandCensus())
    }

    @Test
    fun `backed census combines current diagonal and scalar residuals without decoding masks`() {
        val plain = any(t)
        val exact = m.factsOf(PathFact(output, listOf(f), Tail.EXACT, MarkSlot.Concrete(t)),
            ExclusionSet.Empty, Layer.DEMAND) as TaintTree
        val cross = any(u, listOf(g))
        val mixedRoot = m.taintAlg.mergeAdd(m.taintAlg.mergeAdd(plain.root, exact.root), cross.root)
        val mixed = m.taintTree(output, Layer.DEMAND, mixedRoot, anyTail = Tail.ANY, nonSubsumable = exact.root)
        val store = RunSummaryStore(m, flowBacked = true)
        store.add(initial(), mixed)
        store.add(initial(MarkSlot.Concrete(u)), any(u))
        assertEquals(RelationCensus(concreteOutputMemberships = 4, protectedOutputMemberships = 1,
            diagonalGeometryRows = 1, diagonalMarkRows = 2, scalarConcreteRows = 1), store.census())
        store.add(initial(MarkSlot.STAR), m.flowTree(output, Layer.DEMAND, ExclusionSet.Empty, MarkSet.EMPTY,
            FlowAlgebra.prepend(m, m.path(listOf(f)), FlowAlgebra.LEAF_NODE), Tail.ANY))
        assertEquals(RelationCensus(concreteOutputMemberships = 2, protectedOutputMemberships = 1,
            scalarConcreteRows = 1, flowOutputAnnotations = 1), store.census())
        assertEquals(RelationCensus.ZERO, store.demandCensus())
    }

    @Test
    fun `counts aggregate as numeric values without owner references`() {
        val left = RelationCensus(2, 1, 1, 2, 3, 4)
        val right = RelationCensus(3, 2, 4, 5, 6, 7)
        assertEquals(RelationCensus(5, 3, 5, 7, 9, 11), left + right)
        assertEquals(left, RelationCensus.ZERO + left)
        assertEquals(RelationCensus.ZERO, RunSummaryStore(m, flowBacked = true).census())
        assertEquals(RelationCensus.ZERO, DiagonalRelations(m).census())
    }

    @Test
    fun `census is stack safe and cancellation does not mutate stored rows`() {
        val store = DiagonalRelations(m)
        store.add(initial(), any(t, List(32768) { f }))
        val expected = RelationCensus(concreteOutputMemberships = 1, diagonalGeometryRows = 1, diagonalMarkRows = 1)
        assertEquals(expected, store.census())
        fixture.cancellation.cancel()
        try {
            assertFailsWith<Cancellation.Cancelled> { store.census() }
            assertFailsWith<Cancellation.Cancelled> { RunSummaryStore(m).census() }
        } finally { fixture.cancellation.activate() }
        assertEquals(expected, store.census())
        assertEquals(1, store.all().count())
    }
}
