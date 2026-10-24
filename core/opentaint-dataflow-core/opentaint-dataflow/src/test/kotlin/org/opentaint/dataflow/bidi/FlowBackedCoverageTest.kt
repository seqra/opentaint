package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class FlowBackedCoverageTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val input = AccessPathBase.Argument(0)
    private val output = AccessPathBase.Return

    private fun initial(tail: Tail = Tail.STAR, e: ExclusionSet = ExclusionSet.Empty,
                        mark: MarkSlot = MarkSlot.Concrete(t), path: List<Int> = emptyList()) =
        m.initial(input, m.path(path), tail, e, mark)

    private fun flow(paths: List<List<Int>>, layer: Layer = Layer.DEMAND,
                     tail: Tail = Tail.ANY, excluded: MarkSet = MarkSet.EMPTY,
                     base: AccessPathBase = output): FlowTree {
        val root = paths.map { FlowAlgebra.prepend(m, m.path(it), FlowAlgebra.LEAF_NODE) }
            .reduce { a, b -> FlowAlgebra.mergeAdd(a, b) }
        return m.flowTree(base, layer, ExclusionSet.Empty, excluded, root, tail)
    }

    private fun taint(path: List<Int>, mark: TaintMark = t, tail: Tail = Tail.ANY,
                      layer: Layer = Layer.DEMAND): TaintTree =
        m.factsOf(PathFact(output, path, tail, MarkSlot.Concrete(mark)), ExclusionSet.Empty, layer) as TaintTree

    private fun union(a: TaintTree, b: TaintTree): TaintTree =
        m.taintTree(a.base, a.layer, m.taintAlg.mergeAdd(a.root, b.root), a.exclusion, a.anyTail)

    @Test
    fun `a FLOW tree covers one path through an annotated prefix only`() {
        val tree = flow(listOf(listOf(f), listOf(g, h)))
        assertTrue(flowCoversAny(m, tree, output, intArrayOf(g, h, f), t, Layer.DEMAND))
        assertTrue(flowCoversAny(m, tree, output, intArrayOf(f), t, Layer.DEMAND))
        assertFalse(flowCoversAny(m, tree, output, intArrayOf(g), t, Layer.DEMAND))
        assertFalse(flowCoversAny(m, tree, output, intArrayOf(g, f), t, Layer.DEMAND))
        assertFalse(flowCoversAny(m, tree, output, intArrayOf(), t, Layer.DEMAND))
        assertTrue(flowCoversAny(m, flow(listOf(emptyList(), listOf(g, h))), output,
            intArrayOf(g, f), t, Layer.DEMAND))
    }

    @Test
    fun `mark layer base and supported tail gates are independent`() {
        val path = intArrayOf(f, g)
        assertFalse(flowCoversAny(m, flow(listOf(listOf(f)), excluded = MarkSet.of(t)),
            output, path, t, Layer.DEMAND))
        assertTrue(flowCoversAny(m, flow(listOf(listOf(f)), excluded = MarkSet.of(u)),
            output, path, t, Layer.DEMAND))
        assertFalse(flowCoversAny(m, flow(listOf(listOf(f))), output, path, t, Layer.NORMAL))
        assertTrue(flowCoversAny(m, flow(listOf(listOf(f)), layer = Layer.NORMAL),
            output, path, t, Layer.DEMAND))
        assertFalse(flowCoversAny(m, flow(listOf(listOf(f)), base = input), output, path, t, Layer.DEMAND))
        assertFalse(flowCoversAny(m, flow(listOf(listOf(f)), tail = Tail.STAR), output, path, t, Layer.DEMAND))
    }

    @Test
    fun `initial mapping admits canonical full STAR hypotheses only`() {
        val marked = initial(path = listOf(f))
        val expected = initial(mark = MarkSlot.STAR, path = listOf(f))
        assertSame(expected, flowInitialForCoverage(m, marked))
        assertNull(flowInitialForCoverage(m, m.zero))
        assertNull(flowInitialForCoverage(m, initial(tail = Tail.EXACT)))
        assertNull(flowInitialForCoverage(m, initial(tail = Tail.ANY)))
        assertNull(flowInitialForCoverage(m, initial(e = ExclusionSet.of(g))))
        assertNull(flowInitialForCoverage(m, expected))
        assertNull(flowInitialForCoverage(m, initial(mark = MarkSlot.Concrete(m.marks.runtimeAtom(t, MarkMode.GROUP)))))
        assertNull(flowInitialForCoverage(m, m.premiseOf(listOf(marked, initial(mark = MarkSlot.Concrete(u))))))
        val foreign = StoreFixtures().manager
        assertNull(flowInitialForCoverage(foreign, marked))
    }

    @Test
    fun `pruning removes only covered diagonal ANY memberships`() {
        val facts = union(union(taint(listOf(f, h)), taint(listOf(g))),
            union(taint(listOf(f), u), taint(listOf(f), tail = Tail.EXACT)))
        val remaining = assertNotNull(removeFlowCoveredAny(m, initial(), facts,
            listOf(flow(listOf(listOf(f))))))
        val decoded = fixture.ops.leaves(remaining).map { it.fact }.toSet()
        assertEquals(setOf(
            PathFact(output, listOf(g), Tail.ANY, MarkSlot.Concrete(t)),
            PathFact(output, listOf(f), Tail.ANY, MarkSlot.Concrete(u)),
            PathFact(output, listOf(f), Tail.EXACT, MarkSlot.Concrete(t))), decoded)
        assertNull(removeFlowCoveredAny(m, initial(), taint(listOf(f, h)), listOf(flow(listOf(listOf(f))))))
        val must = taint(listOf(f), tail = Tail.ANY_TAINT, layer = Layer.NORMAL)
        assertSame(must, removeFlowCoveredAny(m, initial(), must,
            listOf(flow(listOf(listOf(f)), layer = Layer.NORMAL))))
    }

    @Test
    fun `protection preserves overlapping exact and ANY regions without protecting other marks`() {
        val tree = flow(listOf(emptyList()))
        val facts = union(taint(listOf(f)), taint(listOf(g)))
        val protectedChild = taint(listOf(f, h), tail = Tail.EXACT).root
        val remaining = assertNotNull(removeFlowCoveredAny(m, initial(), facts, listOf(tree), protectedChild))
        assertEquals(listOf(listOf(f)), fixture.ops.leaves(remaining).map { it.fact.path }.toList())
        assertNotNull(removeFlowCoveredAny(m, initial(), taint(listOf(f, h)), listOf(tree), taint(listOf(f)).root))
        assertNull(removeFlowCoveredAny(m, initial(), taint(listOf(f, h)), listOf(tree),
            taint(listOf(f), tail = Tail.EXACT).root))
        assertNull(removeFlowCoveredAny(m, initial(), taint(listOf(f)), listOf(tree), taint(listOf(f), u).root))
    }

    @Test
    fun `prefix lookup agrees with a finite scalar path oracle`() {
        val paths = listOf(emptyList(), listOf(f), listOf(g), listOf(f, g), listOf(g, h))
        for (mask in 1 until (1 shl paths.size)) {
            val selected = paths.filterIndexed { i, _ -> mask and (1 shl i) != 0 }
            val tree = flow(selected)
            for (path in paths + listOf(listOf(f, g, h), listOf(g, f))) {
                val covered = selected.any { prefix -> path.take(prefix.size) == prefix }
                assertEquals(covered, flowCoversAny(m, tree, output, path.toIntArray(), t, Layer.DEMAND))
                val result = removeFlowCoveredAny(m, initial(), taint(path), listOf(tree))
                assertEquals(!covered, result != null)
            }
        }
    }

    @Test
    fun `deep paths and cancellation use bounded stack traversal`() {
        val path = List(32768) { f }
        val tree = flow(listOf(path.dropLast(1)))
        assertTrue(flowCoversAny(m, tree, output, path.toIntArray(), t, Layer.DEMAND))
        val facts = taint(path)
        assertNull(removeFlowCoveredAny(m, initial(), facts, listOf(tree)))
        fixture.cancellation.cancel()
        try {
            assertFailsWith<Cancellation.Cancelled> {
                flowCoversAny(m, tree, output, path.toIntArray(), t, Layer.DEMAND)
            }
            assertFailsWith<Cancellation.Cancelled> { removeFlowCoveredAny(m, initial(), facts, listOf(tree)) }
        } finally {
            fixture.cancellation.activate()
        }
    }
}
