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
            assertEquals(setOf(flowEntry.copy(fact = flowEntry.fact.copy(tail = Tail.EXACT))), emit(flowEntry, actual))
            assertEquals(setOf(p(listOf(f), Tail.ANY, MarkSlot.STAR)), emit(p(listOf(f), Tail.ANY, MarkSlot.STAR), actual))
        }
    }

    @Test
    fun `STAR entry is a real meet and must input stays must with both exclusions`() {
        val entry = p(listOf(f), Tail.STAR, e = ExclusionSet.of(h))
        val builder = DemandStore.Builder(m)
        assertTrue(builder.add(fixture.method, DemandPattern(entry, p(base = ret))))
        for (tail in listOf(Tail.STAR, Tail.ANY_TAINT)) {
            val actual = p(listOf(f), tail, e = ExclusionSet.of(g))
            assertEquals(setOf(p(listOf(f), Tail.EXACT)), emit(entry, actual))
        }
        assertEquals(setOf(p(listOf(f), Tail.EXACT)), emit(entry, p(listOf(f), Tail.EXACT)))
        assertEquals(setOf(p(listOf(f), Tail.EXACT)), emit(entry, p(listOf(f))))
    }

    @Test
    fun `broader uniform input admits ANY and STAR demand uses a point query`() {
        for (tail in listOf(Tail.STAR, Tail.ANY_TAINT)) {
            val actual = p(tail = tail, e = ExclusionSet.of(f))
            assertEquals(emptySet(), emit(p(listOf(f)), actual))
            assertEquals(if (tail == Tail.ANY_TAINT) setOf(p(listOf(g), tail)) else emptySet(),
                emit(p(listOf(g)), actual))
            assertEquals(setOf(p(listOf(g), Tail.EXACT)),
                emit(p(listOf(g), Tail.STAR, e = ExclusionSet.of(h)), actual))
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
                        if (entry.fact.mark is MarkSlot.Star && initial.fact.tail != Tail.ANY_TAINT)
                            assertEquals(ExclusionSet.Empty, initial.exclusion)
                        assertTrue(insideDemand(initial, entry), "$initial must be contained by $entry")
                        assertTrue(satisfies(initial, actual, restricted = true), "$actual must satisfy $initial")
                    }
                    val policy = RestrictedInitialPolicy(direction = Direction.FORWARD, catalog = m.marks)
                    for (initial in emitted)
                        assertTrue(policy.canEmitInitial(entry, initial), "Emitted initial must have a submitted witness")
                    if (entry.fact.tail == Tail.ANY && actual.fact.tail == Tail.STAR &&
                        entry.fact.path == actual.fact.path)
                        assertTrue(emitted.isEmpty(), "Unrefined ANY cannot be answered with STAR")
                }
            }
        }
    }

    @Test
    fun `below-only RemoveAll cannot create an excluded STAR FLOW demand`() {
        assertFails { Cleaner(x, null, CleanReach.BELOW, null) }
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
