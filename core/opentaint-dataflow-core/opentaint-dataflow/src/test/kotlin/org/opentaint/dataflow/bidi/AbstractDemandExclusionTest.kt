package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Demand copies ignore abstract field E. Actual and native E keep their meaning. */
class AbstractDemandExclusionTest {
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
    private val empty = ExclusionSet.Empty
    private fun e(vararg fields: Int) = ExclusionSet.of(fields)
    private fun p(path: List<Int> = emptyList(), tail: Tail = Tail.STAR, mark: MarkSlot = MarkSlot.STAR,
                  exclusion: ExclusionSet = empty, base: AccessPathBase = x) =
        Pattern(PathFact(base, path, tail, mark), exclusion)
    private fun pack(pattern: Pattern, layer: Layer = if (pattern.fact.tail == Tail.ANY ||
        pattern.fact.tail == Tail.STAR && pattern.fact.mark is MarkSlot.Concrete) Layer.DEMAND else Layer.NORMAL) =
        m.factsOf(pattern.fact, pattern.exclusion, layer)

    @Test
    fun `builder normalizes entry and exit E before exact deduplication`() {
        val raw = DemandPattern(p(exclusion = e(f)), p(exclusion = e(g), base = ret))
        val expected = DemandPattern(p(), p(base = ret))
        val builder = DemandStore.Builder(m)
        assertTrue(builder.add(fixture.method, raw))
        assertFalse(builder.add(fixture.method, expected))
        assertFalse(builder.add(fixture.method, DemandPattern(p(exclusion = e(g, h)), p(exclusion = e(f), base = ret))))
        val stored = builder.build()
        assertEquals(listOf(expected), stored.near(fixture.method, p()))
        assertEquals(listOf(expected), stored.covering(fixture.method, m.initial(p())))
        assertEquals(e(f), raw.entry.exclusion)
        assertEquals(e(g), raw.exit!!.exclusion)
    }

    @Test
    fun `concrete full and group demand exclusions are preserved`() {
        val group = MarkSlot.Concrete(m.marks.group(m.marks.groupOf(t.mark)))
        for (mark in listOf(t, group)) {
            val raw = DemandPattern(p(mark = mark, exclusion = e(f)), p(mark = mark, exclusion = e(g), base = ret))
            val builder = DemandStore.Builder(m)
            assertTrue(builder.add(fixture.method, raw))
            assertEquals(listOf(raw), builder.build().near(fixture.method, p(mark = mark)))
            assertEquals(raw.entry, guidancePattern(raw.entry))
            assertEquals(raw.exit, guidancePattern(raw.exit!!))
        }
    }

    @Test
    fun `abstract excluded demand shares one empty-E FLOW start across actual marks tails and E`() {
        val entry = p(exclusion = e(f))
        val expected = p(tail = Tail.EXACT)
        val marks = listOf(t, u, MarkSlot.STAR, MarkSlot.Star(m.markSetOf(u.mark)))
        val inputs = buildList {
            for (mark in marks) {
                add(p(tail = Tail.EXACT, mark = mark))
                if (mark is MarkSlot.Concrete) {
                    add(p(tail = Tail.ANY, mark = mark))
                    for (exclusion in listOf(empty, e(f), e(g), e(f, g))) {
                        add(p(tail = Tail.ANY_TAINT, mark = mark, exclusion = exclusion))
                        add(p(mark = mark, exclusion = exclusion))
                    }
                } else for (exclusion in listOf(empty, e(f), e(g), e(f, g))) add(p(mark = mark, exclusion = exclusion))
            }
        }
        for (actual in inputs) {
            assertEquals(expected, emit(entry, actual, m.marks), "actual=$actual")
            val packed = pack(actual)
            val started = ops.emit(DemandPattern(entry, null), packed)
            assertEquals(listOf(expected), started.map { it.toPattern() })
            assertEquals(Layer.NORMAL, ops.startFact(started.single()).layer)
            assertTrue(satisfies(expected, actual, restricted = true))
            assertEquals(listOf(actual), ops.leaves(packed).toList())
        }
    }

    @Test
    fun `actual field E still blocks strict descent for STAR FLOW and concrete MUST`() {
        val entry = p(listOf(g), exclusion = e(h))
        val expected = p(listOf(g), tail = Tail.EXACT)
        for (tail in listOf(Tail.STAR, Tail.ANY_TAINT)) for (mark in listOf(t, u, MarkSlot.STAR)) {
            if (tail == Tail.ANY_TAINT && mark is MarkSlot.Star) continue
            val blocked = p(tail = tail, mark = mark, exclusion = e(g))
            val admitted = p(tail = tail, mark = mark, exclusion = e(f))
            assertNull(emit(entry, blocked, m.marks))
            assertTrue(ops.emit(DemandPattern(entry, null), pack(blocked)).isEmpty())
            assertNull(ops.satisfying(pack(blocked), m.initial(expected), ApMode(false, Direction.FORWARD, 2)))
            assertEquals(expected, emit(entry, admitted, m.marks))
            assertEquals(listOf(expected), ops.emit(DemandPattern(entry, null), pack(admitted)).map { it.toPattern() })
            assertEquals(e(g), blocked.exclusion)
            assertEquals(e(f), admitted.exclusion)
        }
    }

    @Test
    fun `whole entry guard ignores demand E but preserves raw output E and mark exclusions`() {
        val initial = m.initial(p())
        val raw = p(exclusion = e(g), mark = MarkSlot.Star(m.markSetOf(u.mark)), base = ret)
        val demand = DemandPattern(p(exclusion = e(f)), p(exclusion = e(h), base = ret))
        assertTrue(insideDemand(initial.toPattern(), demand.entry, m.marks))
        val value = pack(raw)
        assertEquals(listOf(value), ops.restrict(initial, value, demand))
        assertEquals(Conclusion(raw.fact, raw.exclusion, false),
            restrict(initial.toPattern(), Conclusion(raw.fact, raw.exclusion, false), demand, m.marks))
        assertEquals(e(g), (value as FlowTree).exclusion)
        assertEquals(MarkExclusions.of(m.marks, u.mark), value.markExclusion)
    }

    @Test
    fun `abstract exit ignores demand E and keeps exact raw result and its protection`() {
        val initial = m.initial(p(tail = Tail.EXACT, mark = t))
        val raw = pack(p(listOf(f), Tail.EXACT, t, base = ret)) as TaintTree
        val flagged = raw.withProtection(raw.root)
        val demand = DemandPattern(p(tail = Tail.ANY, mark = t), p(exclusion = e(f), base = ret))
        val actual = ops.restrict(initial, flagged, demand).single() as TaintTree
        assertEquals(ops.leaves(raw).toSet(), ops.leaves(actual).toSet())
        assertEquals(Layer.NORMAL, actual.layer)
        assertEquals(actual.root, actual.nonSubsumable)
    }

    @Test
    fun `concrete STAR demand still meets both field exclusions and cannot specialize FLOW`() {
        val entry = p(mark = t, exclusion = e(f))
        val actual = p(tail = Tail.ANY_TAINT, mark = t, exclusion = e(g))
        val expected = p(tail = Tail.EXACT, mark = t)
        assertEquals(expected, emit(entry, actual, m.marks))
        assertEquals(listOf(expected), ops.emit(DemandPattern(entry, null), pack(actual)).map { it.toPattern() })
        assertNull(emit(entry, p(), m.marks))
        val initial = m.initial(p(tail = Tail.EXACT, mark = t))
        val raw = p(tail = Tail.ANY_TAINT, mark = t, exclusion = e(g), base = ret)
        val demand = DemandPattern(p(tail = Tail.ANY, mark = t), p(mark = t, exclusion = e(f), base = ret))
        assertEquals(listOf(raw.copy(exclusion = e(f, g))), ops.restrict(initial, pack(raw), demand)
            .flatMap { ops.leaves(it).toList() })
    }

    @Test
    fun `guidance copies clear abstract E while native record E and matching remain intact`() {
        val original = p(exclusion = e(f))
        val conclusion = p(exclusion = e(g), base = ret)
        val initial = m.initial(original)
        val summaries = RunSummaryStore(m)
        assertNotNull(summaries.add(initial, pack(conclusion)))
        val records = PersistentRecordStore(m)
        records.persist(Direction.FORWARD, sequenceOf(fixture.method to summaries))
        val record = records.byEntry(fixture.method, original).single()
        assertEquals(p(), guidancePattern(original))
        assertEquals(p(base = ret), guidancePattern(conclusion))
        assertEquals(original, record.premise.toPattern())
        assertEquals(listOf(conclusion), ops.leaves(record.conclusion).toList())
        val excludedActual = pack(p(listOf(f), Tail.EXACT, t))
        assertNull(ops.satisfying(excludedActual, record.premise, ApMode(false, Direction.FORWARD, 2), record = true))
        assertEquals(e(f), original.exclusion)
        assertEquals(e(g), conclusion.exclusion)
    }

    @Test
    fun `below-only RemoveAll cannot create an excluded STAR FLOW demand`() {
        assertFails { Cleaner(x, null, CleanReach.BELOW, null) }
    }

}
