package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class FlowBackedProtectionTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)
    private val m = fixture.manager
    private val ops = fixture.ops
    private val mode = ApMode(true, Direction.FORWARD, 1)

    @Test fun `annotation does not change fact or edge identity`(): Unit = with(v) {
        val plain = pack(leaf(p(), Tail.ANY, layer = Layer.DEMAND)) as TaintTree
        val protected = plain.withProtection(plain.root)
        assertEquals(plain, protected)
        assertEquals(plain.hashCode(), protected.hashCode())
        assertNotNull(protected.nonSubsumable)
        assertNull(plain.nonSubsumable)
    }

    @Test fun `same mark assignment checks the triggering conclusion rather than the origin`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt)) as TaintTree
        val original = premise(tail = Tail.STAR, mark = mu)
        val edge = PathEdge(PathFact(x, p(), Tail.EXACT, mt), PathFact(y, p(), Tail.EXACT, mt), ExclusionSet.Empty)
        val out = CollectingOut()
        ops.applyEdge(input, original, edge, false, mode, out, ruleAssignment = true)
        assertTrue(out.results.isNotEmpty())
        assertTrue(out.results.all { it is TaintTree && it.nonSubsumable != null })
    }

    @Test fun `local cross mark cycle protects restored origin`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mu)) as TaintTree
        val original = premise(tail = Tail.STAR, mark = mt)
        val edge = PathEdge(PathFact(x, p(), Tail.EXACT, mu), PathFact(y, p(), Tail.EXACT, mt), ExclusionSet.Empty)
        val out = CollectingOut()
        ops.applyEdge(input, original, edge, false, mode, out, ruleAssignment = true)
        assertNotNull((out.results.single() as TaintTree).nonSubsumable)
    }

    @Test fun `ordinary transport keeps only the protected memberships`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt), leaf(p(), Tail.EXACT, mu)) as TaintTree
        val protected = pack(leaf(p(), Tail.EXACT, mt)) as TaintTree
        val edge = PathEdge(PathFact(x, p(), Tail.STAR, MarkSlot.STAR),
            PathFact(y, p(), Tail.STAR, MarkSlot.STAR), ExclusionSet.Empty)
        val out = CollectingOut()
        ops.applyEdge(input.withProtection(protected.root), premise(tail = Tail.STAR), edge, false, mode, out)
        val result = out.results.single() as TaintTree
        assertEquals(setOf(t), m.taintAlg.foldAll(checkNotNull(result.nonSubsumable)).exact.ids.map(::TaintMark).toSet())
        assertEquals(setOf(t, u), m.taintAlg.foldAll(result.root).exact.ids.map(::TaintMark).toSet())
    }

    @Test fun `selected cleaner protects a surviving selected mark but no unrelated mark`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt), leaf(p(), Tail.EXACT, mu))
        val out = CollectingOut()
        ops.clean(input, premise(tail = Tail.STAR), Cleaner(x, m.path(p(f)), CleanReach.AT_AND_BELOW, t), mode, out)
        val result = out.results.single() as TaintTree
        assertEquals(setOf(t), m.taintAlg.foldAll(checkNotNull(result.nonSubsumable)).exact.ids.map(::TaintMark).toSet())
    }

    @Test fun `field limit moves protection with the bounded marked output`(): Unit = with(v) {
        val input = pack(leaf(p(f, g), Tail.EXACT, mt)) as TaintTree
        val out = CollectingOut()
        ops.limit(input.withProtection(input.root), 1, out)
        val result = out.results.single() as TaintTree
        assertNotNull(result.nonSubsumable)
        assertEquals(result.root, result.nonSubsumable)
    }

    @Test fun `ordinary concrete edge is not a rule assignment`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt))
        val edge = PathEdge(PathFact(x, p(), Tail.EXACT, mt), PathFact(y, p(), Tail.EXACT, mt), ExclusionSet.Empty)
        val out = CollectingOut()
        ops.applyEdge(input, premise(mark = mt), edge, false, mode, out)
        assertNull((out.results.single() as TaintTree).nonSubsumable)
        val rule = CollectingOut()
        ops.applyEdge(input, premise(mark = mu), edge, true, mode, rule, ruleAssignment = true)
        assertNotNull((rule.results.single() as TaintTree).nonSubsumable)
    }

    @Test fun `different mark source without a restoring cycle stays plain`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt))
        val edge = PathEdge(PathFact(x, p(), Tail.EXACT, mt), PathFact(y, p(), Tail.EXACT, mu), ExclusionSet.Empty)
        val out = CollectingOut()
        ops.applyEdge(input, premise(mark = mt), edge, false, mode, out, ruleAssignment = true)
        assertNull((out.results.single() as TaintTree).nonSubsumable)
    }

    @Test fun `summary graft moves only protected input memberships`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt), leaf(p(), Tail.EXACT, mu)) as TaintTree
        val flag = pack(leaf(p(), Tail.EXACT, mt)) as TaintTree
        val summary = pack(flow(p(f)))
        val out = CollectingOut()
        ops.applySummary(input.withProtection(flag.root), premise(tail = Tail.STAR, mark = MarkSlot.STAR), summary, mode, out)
        val result = out.results.single() as TaintTree
        assertEquals(setOf(leaf(p(f), Tail.EXACT, mt)), decoded(checkNotNull(result.protectedPart())))
        assertEquals(setOf(leaf(p(f), Tail.EXACT, mt), leaf(p(f), Tail.EXACT, mu)), decoded(result))
    }

    @Test fun `protected summary marks and caller restoration survive independently`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mu))
        val summary = pack(leaf(p(f), Tail.EXACT, mt, base = y), leaf(p(g), Tail.EXACT, mu, base = y)) as TaintTree
        val flag = pack(leaf(p(g), Tail.EXACT, mu, base = y)) as TaintTree
        val out = CollectingOut()
        ops.applySummary(input, premise(mark = mu), summary.withProtection(flag.root), mode, out,
            original = premise(tail = Tail.STAR, mark = mt))
        val protected = out.results.map { checkNotNull((it as TaintTree).protectedPart()) }.flatMap { decoded(it) }.toSet()
        assertEquals(setOf(leaf(p(f), Tail.EXACT, mt, base = y), leaf(p(g), Tail.EXACT, mu, base = y)), protected)
    }

    @Test fun `selection keeps only surviving protected marks and paths`(): Unit = with(v) {
        val input = pack(leaf(p(f), Tail.EXACT, mt), leaf(p(g), Tail.EXACT, mu)) as TaintTree
        val selected = assertIs<MarkCheck.Holds>(ops.checkMark(input.withProtection(input.root),
            Pattern(PathFact(x, p(f), Tail.EXACT, mt), ExclusionSet.Empty), mode)).facts as TaintTree
        assertEquals(setOf(leaf(p(f), Tail.EXACT, mt)), decoded(checkNotNull(selected.protectedPart())))
        val matched = assertIs<TaintTree>(ops.satisfying(input.withProtection(input.root), premise(p(f), mark = mt), mode))
        assertEquals(setOf(leaf(p(f), Tail.EXACT, mt)), decoded(checkNotNull(matched.protectedPart())))
        assertEquals(setOf(leaf(p(g), Tail.EXACT, mu)), decoded(checkNotNull(ops.withoutMarks(input.withProtection(input.root), marks(t.id)))))
    }

    @Test fun `protection only merge is a real delta and repeat delivery is empty`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt), leaf(p(g), Tail.EXACT, mu)) as TaintTree
        val flag = pack(leaf(p(g), Tail.EXACT, mu)) as TaintTree
        val (stored, delta) = m.mergeAddDelta(input, input.withProtection(flag.root))
        assertEquals(input, stored)
        assertEquals(setOf(leaf(p(g), Tail.EXACT, mu)), decoded(checkNotNull(delta)))
        assertNotNull((delta as TaintTree).nonSubsumable)
        assertNull(m.mergeAddDelta(stored, input.withProtection(flag.root)).second)
    }

    @Test fun `complete cleaner kill has no protected result`(): Unit = with(v) {
        val input = pack(leaf(p(f), Tail.EXACT, mt)) as TaintTree
        val out = CollectingOut()
        ops.clean(input.withProtection(input.root), premise(tail = Tail.STAR),
            Cleaner(x, m.path(p(f)), CleanReach.AT_AND_BELOW, t), mode, out)
        assertTrue(out.results.isEmpty())
    }

    @Test fun `later and GROUP rule paths protect same atom assignments`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt))
        val edge = PathEdge(PathFact(x, p(), Tail.EXACT, mt), PathFact(y, p(), Tail.EXACT, mt), ExclusionSet.Empty)
        val out = CollectingOut()
        ops.applyEdge(input, premise(mark = mt), edge, false, ApMode(false, Direction.FORWARD, 2), out, ruleAssignment = true)
        assertTrue(out.results.isNotEmpty())
        assertTrue(out.results.all { (it as TaintTree).nonSubsumable != null })
        val grouped = CollectingOut()
        val groupMode = ApMode(true, Direction.FORWARD, 1, MarkMode.GROUP)
        ops.applyEdge(ops.runtimeFact(input, groupMode), premise(mark = mt), edge, false,
            groupMode, grouped, ruleAssignment = true)
        assertTrue(grouped.results.isNotEmpty())
        assertTrue(grouped.results.all { (it as TaintTree).nonSubsumable != null })
    }

    @Test fun `bulk selected cleaner keeps old flags and protects only its surviving selected marks`(): Unit = with(v) {
        val input = pack(leaf(p(), Tail.EXACT, mt), leaf(p(), Tail.EXACT, mu)) as TaintTree
        val flag = pack(leaf(p(), Tail.EXACT, mu)) as TaintTree
        val out = CollectingOut()
        ops.cleanSelectedFullMask(input.withProtection(flag.root), premise(tail = Tail.STAR),
            Cleaner(x, m.path(p(f)), CleanReach.AT_AND_BELOW, t), m.markSetOf(t), mode,
            { fail("A concrete cleaner cannot request another mark") }, out)
        val result = out.results.single() as TaintTree
        assertEquals(result.root, result.nonSubsumable)
    }
}
