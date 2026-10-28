package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

/** Literal boundary expectations, with scalar and packed adapters checked together. */
class RestrictedDemandBoundaryTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val ops = fixture.ops
    private val x = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val h = fixture.field("h")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private fun p(path: List<Int> = emptyList(), tail: Tail = Tail.ANY, mark: MarkSlot = t,
                  e: ExclusionSet = ExclusionSet.Empty, base: AccessPathBase = x) =
        Pattern(PathFact(base, path, tail, mark), e)
    private fun emit(entry: Pattern, actual: Pattern): Set<Pattern> {
        val demand = DemandPattern(entry, null)
        val layer = if (actual.fact.tail == Tail.ANY || actual.fact.tail == Tail.STAR && actual.fact.mark is MarkSlot.Concrete)
            Layer.DEMAND else Layer.NORMAL
        val packed = m.factsOf(actual.fact, actual.exclusion, layer)
        val result = ops.emit(demand, packed).map { it.toPattern() }.toSet()
        assertEquals(setOfNotNull(org.opentaint.dataflow.bidi.ap.emit(entry, actual, m.marks)), result)
        return result
    }

    @Test
    fun `entry emission cannot obtain concrete T from FLOW but abstract entries share FLOW`() {
        val flowEntry = p(listOf(f), Tail.STAR, MarkSlot.STAR)
        val concreteEntry = p(listOf(f))
        val flowExcludingU = MarkSlot.Star(m.markSetOf(u.mark))
        for (actualMark in listOf(t, u, MarkSlot.STAR, flowExcludingU)) {
            val actual = p(listOf(f), Tail.ANY, actualMark)
            assertEquals(if (actualMark == t) setOf(actual) else emptySet(), emit(concreteEntry, actual))
            assertEquals(setOf(flowEntry), emit(flowEntry, actual))
            assertEquals(setOf(flowEntry), emit(p(listOf(f), Tail.ANY, MarkSlot.STAR), actual))
        }
    }

    @Test
    fun `STAR entry is a real meet and must input stays must with both exclusions`() {
        val entry = p(listOf(f), Tail.STAR, e = ExclusionSet.of(h))
        val builder = DemandStore.Builder(m)
        assertTrue(builder.add(fixture.method, DemandPattern(entry, p(base = ret))))
        for (tail in listOf(Tail.STAR, Tail.ANY_TAINT)) {
            val actual = p(listOf(f), tail, e = ExclusionSet.of(g))
            assertEquals(setOf(p(listOf(f), tail, e = ExclusionSet.of(intArrayOf(g, h)))), emit(entry, actual))
        }
        assertEquals(setOf(p(listOf(f), Tail.EXACT)), emit(entry, p(listOf(f), Tail.EXACT)))
        assertEquals(setOf(entry), emit(entry, p(listOf(f))))
    }

    @Test
    fun `descent forgets only ancestor exclusion and retains demand exclusion at new path`() {
        for (tail in listOf(Tail.STAR, Tail.ANY_TAINT)) {
            val actual = p(tail = tail, e = ExclusionSet.of(f))
            assertEquals(emptySet(), emit(p(listOf(f)), actual))
            assertEquals(setOf(p(listOf(g), tail)), emit(p(listOf(g)), actual))
            val result = emit(p(listOf(g), Tail.STAR, e = ExclusionSet.of(h)), actual).single()
            assertEquals(p(listOf(g), tail, e = ExclusionSet.of(h)), result)
            assertTrue(covers(result, p(listOf(g, f), Tail.EXACT)))
            assertFalse(covers(result, p(listOf(g, h), Tail.EXACT)))
            assertEquals(ExclusionSet.of(f), actual.exclusion)
        }
    }

    @Test
    fun `legal entry matrix preserves concrete coverage and has equal scalar and packed initials`() {
        val paths = listOf(emptyList(), listOf(f), listOf(g), listOf(f, f), listOf(f, g), listOf(g, f))
        val locations = paths + listOf(listOf(f, f, f), listOf(f, f, g), listOf(f, g, f), listOf(f, g, g),
            listOf(g, f, f), listOf(g, f, g))
        for (entryPath in paths) {
            val entries = listOf(p(entryPath, Tail.EXACT), p(entryPath), p(entryPath, Tail.STAR),
                p(entryPath, Tail.STAR, e = ExclusionSet.of(f)), p(entryPath, mark = u),
                p(entryPath, mark = MarkSlot.STAR), p(entryPath, Tail.STAR, MarkSlot.STAR),
                p(entryPath, Tail.STAR, MarkSlot.STAR, ExclusionSet.of(f)))
            for (actualPath in paths) {
                val actuals = listOf(p(actualPath, Tail.EXACT), p(actualPath),
                    p(actualPath, Tail.STAR), p(actualPath, Tail.STAR, e = ExclusionSet.of(f)),
                    p(actualPath, Tail.ANY_TAINT), p(actualPath, Tail.ANY_TAINT, e = ExclusionSet.of(f)),
                    p(actualPath, Tail.EXACT, u), p(actualPath, Tail.STAR, MarkSlot.STAR),
                    p(actualPath, Tail.STAR, MarkSlot.STAR, ExclusionSet.of(f)),
                    p(actualPath, mark = MarkSlot.Star(m.markSetOf(u.mark))))
                for (entry in entries) for (actual in actuals) {
                    val emitted = emit(entry, actual)
                    for (initial in emitted) {
                        if (entry.fact.mark is MarkSlot.Star) assertEquals(ExclusionSet.Empty, initial.exclusion)
                        assertTrue(insideDemand(initial, entry), "$initial must be contained by $entry")
                        assertTrue(satisfies(initial, actual, restricted = true), "$actual must satisfy $initial")
                    }
                    val eligible = entry.fact.mark is MarkSlot.Star || actual.fact.mark is MarkSlot.Concrete &&
                        markSub(entry.fact.mark, actual.fact.mark, m.marks)
                    if (!eligible) {
                        assertTrue(emitted.isEmpty(), "Concrete demand cannot specialize FLOW or another mark")
                        continue
                    }
                    for (path in locations) for (mark in listOf(t, u)) {
                        val location = p(path, Tail.EXACT, mark)
                        if (covers(entry, location, m.marks) && covers(actual, location, m.marks))
                            assertTrue(emitted.any { covers(it, location, m.marks) },
                                "Missing $location in emitted=$emitted; entry=$entry, actual=$actual")
                    }
                }
            }
        }
    }

    @Test
    fun `strong update then partial all-mark cleaning can produce excluded STAR FLOW demand`() {
        val initialPattern = p(tail = Tail.STAR, mark = MarkSlot.STAR)
        val initial = m.initial(initialPattern)
        val mode = ApMode(false, Direction.FORWARD, 2)
        val write = PathEdge(initialPattern.fact, initialPattern.fact, ExclusionSet.of(f))
        val written = CollectingOut()
        ops.applyEdge(ops.startFact(initial), initial, write, statementEdge = true, mode, written)
        val afterWrite = written.results.single()
        assertEquals(setOf(p(tail = Tail.STAR, mark = MarkSlot.STAR, e = ExclusionSet.of(f))),
            ops.leaves(afterWrite).toSet())
        assertEquals(Layer.NORMAL, afterWrite.layer)
        val cleaned = CollectingOut()
        ops.clean(afterWrite, initial, Cleaner(x, null, CleanReach.BELOW, null), mode, cleaned)
        val afterClean = cleaned.results.single()
        assertEquals(Layer.DEMAND, afterClean.layer)
        val expected = p(tail = Tail.STAR, mark = MarkSlot.STAR, e = ExclusionSet.of(f))
        assertEquals(setOf(expected), ops.leaves(afterClean).toSet())
        // This is an actual producer, not a malformed caller-supplied demand value.
        val returned = CollectingOut()
        ops.applyEdge(afterClean, initial, PathEdge(initialPattern.fact,
            initialPattern.fact.copy(base = ret), ExclusionSet.Empty), true, mode, returned)
        val exit = ops.leaves(returned.results.single()).single()
        assertEquals(expected.copy(fact = expected.fact.copy(base = ret)), exit)
        val builder = DemandStore.Builder(m)
        assertTrue(builder.add(fixture.method, DemandPattern(exit, initialPattern)))
        assertEquals(ExclusionSet.Empty, builder.build().near(fixture.method, exit).single().entry.exclusion)
    }

    @Test
    fun `concrete exit gate keeps correlated FLOW whole and honors excluded marks`() {
        val initial = m.initial(p(tail = Tail.STAR, mark = MarkSlot.STAR))
        val entry = p(mark = MarkSlot.STAR)
        val demand = DemandPattern(entry, p(tail = Tail.EXACT, mark = t, base = ret))
        for ((excluded, allowed) in listOf(MarkSet.EMPTY to true,
            m.markSetOf(t.mark) to false, m.markSetOf(u.mark) to true)) {
            val conclusion = m.factsOf(p(tail = Tail.STAR, mark = MarkSlot.Star(excluded), base = ret).fact,
                ExclusionSet.Empty, Layer.NORMAL)
            val restricted = ops.restrict(initial, conclusion, demand)
            assertEquals(if (allowed) listOf(conclusion) else emptyList(), restricted)
        }
        // A concrete entry never authorizes this FLOW original, even when the exit agrees.
        val flow = m.factsOf(p(tail = Tail.STAR, mark = MarkSlot.STAR, base = ret).fact,
            ExclusionSet.Empty, Layer.NORMAL)
        assertTrue(ops.restrict(initial, flow, DemandPattern(p(), p(mark = t, base = ret))).isEmpty())
    }
}
