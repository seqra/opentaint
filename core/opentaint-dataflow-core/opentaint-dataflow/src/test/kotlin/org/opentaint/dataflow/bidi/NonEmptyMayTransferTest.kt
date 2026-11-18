package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.testApManager
import org.opentaint.dataflow.bidi.interp.strongKeep
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFails
import kotlin.test.assertIs
import kotlin.test.assertTrue

class NonEmptyMayTransferTest {
    private val manager = testApManager(Cancellation())
    private val ops = ApOps(manager)
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Return
    private val f = manager.accessors.index(FieldAccessor("Box", "f", "Box"))
    private val g = manager.accessors.index(FieldAccessor("Box", "g", "Box"))
    private val t = manager.marks.mark("T")
    private val full = MarkSlot.Concrete(t)
    private val mode = ApMode(false, Direction.FORWARD, 3, demandRefinement = true)
    private val ne = Tail.NON_EMPTY_MAY
    private val empty = ExclusionSet.Empty

    @Test
    fun `real cuts retain a nonempty suffix and literal protection`() {
        val input = manager.selectedProtection(fact(x, listOf(f, g), Tail.EXACT), manager.markSetOf(t))
        val cut = CollectingOut().also { ops.limit(input, 1, true, it) }.results.single()
        assertEquals(pattern(x, listOf(f), ne), ops.leaves(cut).single())
        assertEquals(Layer.DEMAND, cut.layer)
        assertIs<TaintTree>(cut)
        assertEquals(cut.root, cut.nonSubsumable)
        assertFails { manager.initial(pattern(x, listOf(f), ne)) }
        val inLimit = fact(x, listOf(f), Tail.ANY)
        assertEquals(listOf(inLimit), CollectingOut().also { ops.limit(inLimit, 1, true, it) }.results)
    }

    @Test
    fun `protected and plain leaves coalescing at a cut remain separate memberships`() {
        val plain = assertIs<TaintTree>(fact(x, listOf(f, f), Tail.EXACT))
        val flagged = assertIs<TaintTree>(fact(x, listOf(f, g), Tail.EXACT))
        val root = manager.taintAlg.mergeAdd(plain.root, flagged.root, manager.cancellation)
        val both = manager.taintTree(x, Layer.NORMAL, root, nonSubsumable = flagged.root)
        val cut = CollectingOut().also { ops.limit(both, 1, true, it) }.results.filterIsInstance<TaintTree>()
        assertEquals(listOf(false, true), cut.map { it.nonSubsumable != null })
        assertEquals(List(2) { pattern(x, listOf(f), ne) }, leaves(cut))
    }

    @Test
    fun `reads consume unknown suffixes and preserve known prefixes`() {
        val read = PathEdge(pattern(x, listOf(f), Tail.STAR, MarkSlot.STAR).fact,
            pattern(y, emptyList(), Tail.STAR, MarkSlot.STAR).fact, empty)
        assertEquals(listOf(pattern(y, emptyList(), Tail.ANY)), leaves(transfer(fact(x, emptyList(), ne), read)))
        assertEquals(listOf(pattern(y, emptyList(), ne)), leaves(transfer(fact(x, listOf(f), ne), read)))
        assertTrue(transfer(fact(x, emptyList(), Tail.EXACT), read).isEmpty())

        val unknown = fact(x, emptyList(), ne)
        assertEquals(MarkCheck.None, ops.checkMark(unknown, pattern(x, emptyList(), Tail.EXACT), mode))
        val child = assertIs<MarkCheck.Holds>(ops.checkMark(unknown, pattern(x, listOf(f), Tail.EXACT), mode))
        assertEquals(Layer.DEMAND, child.facts.layer)
    }

    @Test
    fun `writes preserve within-limit may and exclude exact flow from a strict child keep`() {
        val write = PathEdge(pattern(y, emptyList(), Tail.STAR, MarkSlot.STAR).fact,
            pattern(x, listOf(f, g), Tail.STAR, MarkSlot.STAR).fact, empty)
        val written = transfer(fact(y, emptyList(), Tail.ANY), write).single()
        assertEquals(pattern(x, listOf(f, g), Tail.ANY), ops.leaves(written).single())
        val bounded = CollectingOut().also { ops.limit(written, 1, true, it) }.results.single()
        assertEquals(pattern(x, listOf(f), ne), ops.leaves(bounded).single())
        val keep = strongKeep(x, listOf(f, g))
        val point = fact(x, emptyList(), Tail.EXACT, MarkSlot.STAR)
        assertTrue(transfer(point, keep[1]).isEmpty())
        val kept = transfer(point, keep[0]).single()
        assertEquals(pattern(x, emptyList(), Tail.EXACT, MarkSlot.STAR, ExclusionSet.of(f)), ops.leaves(kept).single())
        assertEquals(Layer.NORMAL, kept.layer)
    }

    @Test
    fun `coarse nonempty and may retain separate admitted headers`() {
        val owner = ConclusionGroup(manager, manager.newInterners())
        val may = fact(x, emptyList(), Tail.ANY)
        val possibleChild = fact(x, listOf(f), ne)
        owner.addAll(may)
        assertEquals(listOf(possibleChild), owner.addAll(possibleChild))
        assertEquals(setOf(may, possibleChild), owner.all().toSet())
    }

    @Test
    fun `cleaner preserves exact-cleaned uniform support and partitions below survivors`() {
        val must = fact(x, emptyList(), Tail.ANY_TAINT)
        val exact = clean(must, listOf(f, g), CleanReach.EXACT)
        assertEquals(listOf(pattern(x, emptyList(), Tail.ANY_TAINT)), leaves(exact))
        assertTrue(exact.all { it.layer == Layer.NORMAL && (it as TaintTree).nonSubsumable == it.root })
        val below = clean(must, listOf(f, g), CleanReach.BELOW)
        assertEquals(setOf(
            pattern(x, emptyList(), Tail.ANY_TAINT, e = ExclusionSet.of(f)),
            pattern(x, listOf(f), Tail.ANY_TAINT, e = ExclusionSet.of(g)),
            pattern(x, listOf(f, g), Tail.EXACT),
        ), leaves(below).toSet())
        assertTrue(below.all { it.layer == Layer.NORMAL && (it as TaintTree).nonSubsumable == it.root })
        assertTrue(clean(fact(x, emptyList(), ne), emptyList(), CleanReach.BELOW).isEmpty())
        assertEquals(listOf(pattern(x, emptyList(), ne)), leaves(clean(fact(x, emptyList(), ne), emptyList(), CleanReach.EXACT)))
    }

    @Test
    fun `selected flow cleaner splits a packed packet by suffix cones`() {
        val root = FlowAlgebra.mergeAdd(
            FlowAlgebra.LEAF_NODE,
            FlowAlgebra.prepend(manager, manager.path(listOf(g)), FlowAlgebra.LEAF_NODE),
            manager.cancellation,
        )
        val packet = manager.flowTree(x, Layer.NORMAL, empty, MarkSet.EMPTY, root)
        val after = clean(packet, emptyList(), CleanReach.EXACT)
        assertEquals(setOf(
            pattern(x, emptyList(), Tail.STAR, MarkSlot.Star(manager.markSetOf(t))),
            pattern(x, listOf(g), Tail.STAR, MarkSlot.STAR),
        ), leaves(after).toSet())
    }

    private fun transfer(input: Facts, edge: PathEdge): List<Facts> = CollectingOut().also {
        ops.applyEdge(input, manager.zero, edge, true, mode, it)
    }.results

    private fun clean(input: Facts, path: List<Int>, reach: CleanReach): List<Facts> = CollectingOut().also {
        ops.clean(input, manager.zero, Cleaner(x, manager.path(path), reach, t), mode, it)
    }.results

    private fun leaves(inputs: List<Facts>): List<Pattern> = inputs.flatMap { ops.leaves(it).toList() }

    private fun fact(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot = full): Facts =
        manager.factsOf(pattern(base, path, tail, mark).fact, empty, Layer.NORMAL)

    private fun pattern(base: AccessPathBase, path: List<Int>, tail: Tail, mark: MarkSlot = full,
                        e: ExclusionSet = empty): Pattern = Pattern(PathFact(base, path, tail, mark), e)
}
