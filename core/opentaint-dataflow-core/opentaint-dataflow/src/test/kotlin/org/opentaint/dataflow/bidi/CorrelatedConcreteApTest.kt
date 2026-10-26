package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.testApManager
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

/** Correspondence controls for the constructive correlated-concrete AP model. */
class CorrelatedConcreteApTest {
    private val m: ApManager = testApManager(Cancellation())
    private val ops = ApOps(m)
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Return
    private val f = m.accessors.index(FieldAccessor("Box", "f", "Box"))
    private val g = m.accessors.index(FieldAccessor("Box", "g", "Box"))
    private val t = m.marks.mark("T")
    private val mark = MarkSlot.Concrete(t)
    private val empty = ExclusionSet.Empty
    private val initial = m.initial(x, null, Tail.STAR, empty, mark)
    private val modes = listOf(ApMode(true, Direction.FORWARD, 3, markMode = MarkMode.FULL),
        ApMode(false, Direction.BACKWARD, 3), ApMode(false, Direction.FORWARD, 3))

    private fun fact(path: List<Int> = emptyList(), tail: Tail = Tail.STAR,
                     e: ExclusionSet = empty, base: AccessPathBase = x): TaintTree =
        m.factsOf(PathFact(base, path, tail, mark), e, Layer.DEMAND) as TaintTree

    private fun copy(from: List<Int>, to: List<Int>, exclusion: ExclusionSet = empty) =
        PathEdge(PathFact(x, from, Tail.STAR, MarkSlot.STAR),
            PathFact(y, to, Tail.STAR, MarkSlot.STAR), exclusion)

    @Test fun `STAR seed retains its tail and E in all runs and mark modes`() {
        val e = ExclusionSet.of(g)
        val i = m.initial(x, m.path(listOf(f)), Tail.STAR, e, mark)
        for (mode in modes + ApMode(true, Direction.FORWARD, 3, markMode = MarkMode.GROUP)) {
            val seed = ops.startFact(i, mode) as TaintTree
            assertEquals(Tail.STAR, seed.anyTail)
            assertEquals(e, seed.exclusion)
            assertEquals(Layer.DEMAND, seed.layer)
            assertNull(seed.nonSubsumable)
            assertEquals(Tail.STAR, startFact(i.toPattern()).fact.tail)
        }
    }

    @Test fun `copy at tracked prefix preserves STAR while deeper read loses correlation`() {
        for (mode in modes) {
            val at = CollectingOut()
            ops.applyEdge(fact(), initial, copy(emptyList(), listOf(g)), true, mode, at)
            assertEquals(listOf(Pattern(PathFact(y, listOf(g), Tail.STAR, mark), empty)),
                at.results.flatMap { ops.leaves(it).toList() })
            val read = CollectingOut()
            ops.applyEdge(fact(), initial, copy(listOf(f), emptyList()), true, mode, read)
            assertEquals(Tail.ANY, (read.results.single() as TaintTree).anyTail)
        }
    }

    @Test fun `known copy remainder retains STAR and its own exclusion`() {
        val e = ExclusionSet.of(g)
        val out = CollectingOut()
        ops.applyEdge(fact(listOf(f), e = e), initial, copy(emptyList(), emptyList()), true,
            modes[1], out)
        assertEquals(listOf(Pattern(PathFact(y, listOf(f), Tail.STAR, mark), e)),
            out.results.flatMap { ops.leaves(it).toList() })
    }

    @Test fun `run-1 exclusion cover preserves STAR and later runs keep E`() {
        val e = ExclusionSet.of(f)
        for (mode in modes) {
            val out = CollectingOut()
            ops.applyEdge(fact(), initial, copy(emptyList(), emptyList(), e), true, mode, out)
            val result = out.results.single() as TaintTree
            assertEquals(Tail.STAR, result.anyTail)
            assertEquals(if (mode.run1) empty else e, result.exclusion)
        }
    }

    @Test fun `STAR summary selects correlated inputs and compiles shared exclusions`() {
        val e = ExclusionSet.of(g)
        val i = m.initial(x, null, Tail.STAR, e, mark)
        val input = fact(e = e)
        val summary = fact(listOf(f), e = e, base = y)
        for (mode in modes.drop(1)) {
            assertNotNull(ops.satisfying(input, i, mode))
            val out = CollectingOut()
            ops.applySummary(input, i, summary, mode, out)
            assertEquals(listOf(Pattern(PathFact(y, listOf(f), Tail.STAR, mark), e)),
                out.results.flatMap { ops.leaves(it).toList() })
        }
    }

    @Test fun `STAR storage admits a late flag once and never consumes exact or must`() {
        val group = TaintGroup(m, m.newInterners().taint)
        val plain = fact()
        assertNotNull(group.add(plain))
        assertNull(group.add(plain))
        val flagged = plain.withProtection(plain.root)
        assertNotNull(group.add(flagged)?.nonSubsumable)
        repeat(5) { assertNull(group.add(flagged)) }
        assertNotNull(group.add(fact(tail = Tail.EXACT)))
        assertNotNull(group.add(fact(tail = Tail.ANY_TAINT)))
        assertNotNull(group.add(fact(listOf(f))))
    }

    @Test fun `selected below-root cleaner retains only the exact protected root`() {
        for (mode in modes) {
            val out = CollectingOut()
            ops.clean(fact(), initial, Cleaner(x, null, CleanReach.BELOW, t), mode, out)
            val result = out.results.single() as TaintTree
            assertEquals(listOf(Pattern(PathFact(x, emptyList(), Tail.EXACT, mark), empty)),
                ops.leaves(result).toList())
            assertNotNull(result.nonSubsumable)
        }
    }

    @Test fun `GROUP projection keeps the protection mask and STAR geometry`() {
        val input = fact(listOf(f), e = ExclusionSet.of(g)).let { it.withProtection(it.root) }
        val result = m.runtimeFact(input, ApMode(true, Direction.FORWARD, 3,
            markMode = MarkMode.GROUP)) as TaintTree
        assertEquals(Tail.STAR, result.anyTail)
        assertEquals(input.exclusion, result.exclusion)
        assertEquals(result.root, result.nonSubsumable)
        assertNotEquals(input.root, result.root)
    }
}
