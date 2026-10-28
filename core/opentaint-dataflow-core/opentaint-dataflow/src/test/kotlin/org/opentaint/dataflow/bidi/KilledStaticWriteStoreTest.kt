package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class KilledStaticWriteStoreTest {
    private val f = StoreFixtures()
    private val ap = f.manager
    private val interner = StaticWriteKeyInterner(ap)
    private val path = listOf(ap.accessors.index(ClassStaticAccessor("C")), f.field("f"))
    private val otherPath = listOf(path.first(), f.field("g"))
    private val t = MarkSlot.Concrete(f.mark("T"))
    private val u = MarkSlot.Concrete(f.mark("U"))
    private fun original(mark: MarkSlot = t, base: AccessPathBase = AccessPathBase.Argument(0)) =
        ap.initial(f.pattern(base, tail = Tail.STAR, mark = mark))
    private fun value(mark: MarkSlot = t, tail: Tail = Tail.STAR, at: List<Int> = path) =
        f.fact(STATIC, at, tail, mark, layer = Layer.DEMAND)
    private fun store(owner: MethodKey = f.method) = KilledStaticWriteStore(owner, ap, f.ops, interner)

    @Test fun `lost candidates retain original mark mapping and exact output geometry`() {
        val store = store()
        val origin = original(t)
        store.observe(origin, value(u, Tail.STAR))
        store.observe(origin, value(u, Tail.ANY))
        store.observe(original(t, AccessPathBase.Argument(1)), value(u))
        val frozen = store.freeze(emptySequence(), emptySequence())
        assertEquals(3, frozen.observedCount)
        assertEquals(frozen.observedRows().toSet(), frozen.lostRows().toSet())
        assertEquals(setOf(Tail.STAR, Tail.ANY), frozen.lostRows().map { it.result.fact.tail }.toSet())
        assertTrue(frozen.lostRows().all { it.original.mark == t && it.result.fact.mark == u })
        assertEquals(setOf(AccessPathBase.Argument(0), AccessPathBase.Argument(1)),
            frozen.lostRows().map { it.original.base }.toSet())
    }

    @Test fun `packed observation matches scalar keys and duplicate membership is admitted once`() {
        val a = value(t)
        val b = value(u, Tail.STAR, otherPath)
        val packed = ap.mergeAddDelta(a, b).first
        val store = store()
        store.observe(ap.zero, packed)
        store.observe(ap.zero, a)
        store.observe(ap.zero, b)
        val frozen = store.freeze(emptySequence(), emptySequence())
        assertEquals(2, frozen.observedCount)
        assertEquals(2, frozen.peakCount)
        assertEquals(f.ops.leaves(packed).toSet(), frozen.observedRows().map { it.result }.toSet())
        assertTrue(frozen.observedRows().all { it.original === ap.zero })
        val shared = store(f.key("other owner"))
        shared.observe(ap.zero, packed)
        val other = shared.freeze(emptySequence(), emptySequence())
        assertEquals(frozen.observedIds().toSet(), other.observedIds().toSet())
        assertNotEquals(frozen.owner, other.owner)
    }

    @Test fun `final common and private B keys remove only their exact candidates`() {
        val store = store()
        val ordinary = original()
        val static = ap.initial(f.pattern(STATIC, path, Tail.STAR, t))
        store.observe(ordinary, value())
        store.observe(static, value(u, at = otherPath))
        store.observe(ordinary, value(u))
        val bridge = StaticGuidanceEdge.of(static.toPattern(), f.ops.leaves(value(u, at = otherPath)).single())
        val frozen = store.freeze(sequenceOf(ordinary to value()), sequenceOf(bridge))
        assertEquals(3, frozen.observedCount)
        assertEquals(listOf(u), frozen.lostRows().map { it.result.fact.mark }.toList())
        assertTrue(frozen.lostRows().all { it.original === ordinary })
    }

    @Test fun `raw excluded FLOW survives interning while final guide equality uses canonical copies`() {
        val excluded = MarkSlot.Star(MarkSet.of(f.mark("T")))
        val flow = original(MarkSlot.STAR)
        val store = store()
        val raw = value(excluded)
        store.observe(flow, raw)
        val frozen = store.freeze(sequenceOf(flow to value(MarkSlot.STAR)), emptySequence())
        assertEquals(0, frozen.lostCount)
        assertEquals(excluded, frozen.observedRows().single().result.fact.mark)
        assertEquals(MarkSlot.STAR, frozen.observedRows().single().guidance().to.fact.mark)
    }

    @Test fun `interner keeps raw field exclusions and genuine ZERO without sharing their originals`() {
        val origin = original()
        val raw = f.pattern(STATIC, path, Tail.STAR, u, ExclusionSet.of(f.field("g")))
        val id = interner.intern(origin, raw)
        val decoded = interner.row(id)
        assertSame(origin, decoded.original)
        assertEquals(raw, decoded.result)
        val zeroId = interner.intern(ap.zero, raw)
        assertNotEquals(id, zeroId)
        assertSame(ap.zero, interner.row(zeroId).original)
    }

    @Test fun `a marked survivor later erased by FLOW stays pending until the final snapshot`() {
        val store = store()
        val markedOrigin = original()
        val flowOrigin = original(MarkSlot.STAR)
        val marked = value()
        val flow = value(MarkSlot.STAR)
        val common = RunSummaryStore(ap, flowBacked = true)
        store.observe(markedOrigin, marked)
        common.add(markedOrigin, marked)
        assertTrue(common.all().any { it.first === markedOrigin })
        assertEquals(1, store.candidateCount)
        common.add(flowOrigin, flow)
        store.observe(flowOrigin, flow)
        assertTrue(common.all().none { it.first === markedOrigin })
        val frozen = store.freeze(common.all(), emptySequence())
        assertEquals(2, frozen.observedCount)
        assertEquals(markedOrigin, frozen.lostRows().single().original)
        assertEquals(t, frozen.lostRows().single().result.fact.mark)
    }

    @Test fun `freeze is idempotent and published ID arrays do not mutate the inventory`() {
        val store = store()
        store.observe(original(), value())
        val frozen = store.freeze(emptySequence(), emptySequence())
        val ids = frozen.observedIds()
        ids[0] = -1
        assertEquals(1, frozen.observedRows().count())
        val observedIds = ArrayList<Int>()
        frozen.forEachObservedId(observedIds::add)
        val lostIds = ArrayList<Int>()
        frozen.forEachLostId(lostIds::add)
        assertEquals(frozen.observedIds().toList(), observedIds)
        assertEquals(frozen.lostIds().toList(), lostIds)
        assertEquals(1, store.candidateCount, "Final statistics survive mutable collector release")
        assertSame(frozen, store.freeze(emptySequence(), emptySequence()))
        assertFailsWith<IllegalStateException> { store.observe(original(), value()) }
    }
}
