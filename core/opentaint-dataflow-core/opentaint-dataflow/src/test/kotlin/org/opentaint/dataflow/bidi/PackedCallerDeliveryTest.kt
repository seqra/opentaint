package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.historical.CalleeSubscriptions as ScalarSubscriptions
import org.opentaint.dataflow.bidi.engine.historical.RequestedRow as ScalarRequestedRow
import org.opentaint.dataflow.bidi.engine.historical.RequestRowView as ScalarRequestRowView
import org.opentaint.dataflow.bidi.engine.historical.Run1Slot as ScalarRun1Slot
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Complete consumers see native packets in native posting order, after storage-only packing. */
class PackedCallerDeliveryTest {
    private val f = StoreFixtures()
    private val m = f.manager
    private val x = AccessPathBase.Argument(0)
    private val q = AccessPathBase.Return
    private val a = f.field("a")
    private val b = f.field("b")
    private val t = f.mark("T")
    private val u = f.mark("U")
    private val v = f.mark("V")
    private val mode = ApMode(true, Direction.FORWARD, 3)
    private fun sub(source: TaintMark, path: List<Int>, target: TaintMark = source,
                    stage: Int = 0, scope: BlockScope = BlockScope.ROOT): Subscription {
        val original = m.initial(x, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.Concrete(source))
        return Subscription(f.key("callee"), CallerRef(f.key("caller"), original, Layer.NORMAL,
            f.inst(1), stage, scope), Layer.NORMAL,
            f.fact(q, path, mark = MarkSlot.Concrete(target)))
    }
    private fun pub(path: List<Int>, base: AccessPathBase = q, tail: Tail = Tail.STAR): Publication =
        Publication(m.initial(base, m.path(path), tail, ExclusionSet.Empty, MarkSlot.STAR), f.fact())
    private fun decoded(sub: Subscription): Pair<CallerRef, Pair<GroupKey, Set<Pattern>>> =
        sub.ref to (sub.added.groupKey to f.ops.leaves(sub.added).toSet())
    private fun scalarRows(rows: List<RequestedRow>): List<ScalarRequestedRow> = rows.map {
        ScalarRequestedRow(ScalarRun1Slot.Base(it.slot.base),
            ScalarRequestRowView(RequestMarkSet.EMPTY, it.marks.marks))
    }

    @Test fun `interleaved families and late positions retain first posting order and whole snapshots`() {
        val packed = CalleeSubscriptions(f.ops)
        val scalar = ScalarSubscriptions(f.ops)
        val offers = listOf(
            sub(t, listOf(b)),       // Handle T exists before U, but T arrives at a after U.
            sub(v, listOf(a), stage = 1), // A different family interleaves the common-path postings.
            sub(u, listOf(a)),
            sub(t, listOf(a), target = u),
            sub(t, listOf(a, b), target = v),
        )
        val admissions = ArrayList<Pair<CalleeSubscriptions.Admission, ScalarSubscriptions.Admission>>()
        for (offer in offers) {
            val actual = assertNotNull(packed.admit(offer))
            val expected = assertNotNull(scalar.admit(offer))
            admissions += actual to expected
            assertEquals(decoded(expected.fresh), decoded(actual.fresh))
            assertEquals(expected.growth, actual.growth)
            for (path in listOf(emptyList(), listOf(a), listOf(b), listOf(a, b))) {
                val query = pub(path)
                assertEquals(scalar.candidates(query, 0, mode).map(::decoded).toList(),
                    packed.candidates(query, 0, mode).map(::decoded).toList())
            }
        }
        assertEquals(listOf(v, u, t), packed.candidates(pub(listOf(a)), 0, mode).map {
            ((it.ref.premise as InitialAp).mark as MarkSlot.Concrete).mark
        }.toList())
        for ((actual, expected) in admissions) {
            assertEquals(decoded(expected.current), decoded(actual.current))
            assertEquals(decoded(expected.fresh), decoded(actual.fresh), "Queued deltas never grow with current")
        }
    }

    @Test fun `candidate snapshots stay immutable when a consumer grows another input`() {
        val packed = CalleeSubscriptions(f.ops)
        packed.add(sub(t, listOf(a)))
        packed.add(sub(u, listOf(a)))
        val selected = packed.candidates(pub(emptyList()), 0, mode).iterator()
        val first = selected.next()
        val firstMark = ((first.ref.premise as InitialAp).mark as MarkSlot.Concrete).mark
        val other = if (firstMark == t) u else t
        packed.add(sub(other, listOf(b), target = v))
        val second = selected.next()
        assertEquals(1, f.ops.leaves(second.added).count(), "All snapshots precede the first callback")
        assertFalse(selected.hasNext())
        assertEquals(2, packed.candidates(pub(emptyList()), 0, mode).count())
    }

    @Test fun `request batches share one seen set and forbid reentrant mutation before finally reset`() {
        val packed = CalleeSubscriptions(f.ops)
        val scalar = ScalarSubscriptions(f.ops)
        val offers = listOf(sub(t, listOf(a)), sub(u, listOf(b)), sub(v, listOf(a, b)))
        for (offer in offers) { packed.add(offer); scalar.add(offer) }
        val row = RequestedRow(Run1Slot.Base(q), RequestRowView(RequestMarkSet.of(t)))
        val rows = listOf(row, row)
        val expected = ArrayList<Subscription>()
        val actual = ArrayList<Subscription>()
        scalar.visitRequestBatch(scalarRows(rows), expected::add)
        packed.visitRequestBatch(rows) { input ->
            actual += input
            assertFailsWith<IllegalStateException> { packed.add(sub(t, listOf(b))) }
        }
        assertEquals(expected.map(::decoded), actual.map(::decoded))
        assertEquals(3, actual.size)
        assertFailsWith<IllegalStateException> { packed.visitRequestBatch(rows) { error("visitor") } }
        assertNotNull(packed.add(sub(t, listOf(b))), "finally restores mutation after a failed visitor")
    }

    @Test fun `packed to scalar migration preserves request and publication posting order`() {
        val packed = CalleeSubscriptions(f.ops)
        val scalar = ScalarSubscriptions(f.ops)
        val group = m.marks.group(m.marks.groupOf(t))
        for (offer in listOf(sub(t, listOf(a)), sub(u, listOf(a)), sub(t, listOf(b), target = group))) {
            assertEquals(scalar.add(offer)?.let(::decoded), packed.add(offer)?.let(::decoded))
        }
        val query = pub(emptyList())
        assertEquals(scalar.candidates(query, 0, mode).map(::decoded).toList(),
            packed.candidates(query, 0, mode).map(::decoded).toList())
        val row = RequestedRow(Run1Slot.Base(q), RequestRowView(RequestMarkSet.of(t)))
        val actual = ArrayList<Subscription>()
        val expected = ArrayList<Subscription>()
        packed.visitRequestBatch(listOf(row), actual::add)
        scalar.visitRequestBatch(scalarRows(listOf(row)), expected::add)
        assertEquals(expected.map(::decoded), actual.map(::decoded))
    }

    @Test fun `static class accessor geometry and physical block entries remain separate`() {
        val packed = CalleeSubscriptions(f.ops)
        val scalar = ScalarSubscriptions(f.ops)
        val cls = m.accessors.index(ClassStaticAccessor("C"))
        val scope = BlockScope(BlockId(4), PortId(2))
        val offers = listOf(sub(t, listOf(cls, a)).copy(added = f.fact(STATIC, listOf(cls, a))),
            sub(u, listOf(cls, a)).copy(added = f.fact(STATIC, listOf(cls, a), mark = MarkSlot.Concrete(u))),
            sub(t, listOf(a), scope = scope))
        for (offer in offers) { scalar.add(offer); packed.add(offer) }
        for (query in listOf(pub(emptyList(), STATIC), pub(listOf(cls), STATIC), pub(listOf(a))))
            assertEquals(scalar.candidates(query, 0, mode).map(::decoded).toList(),
                packed.candidates(query, 0, mode).map(::decoded).toList())
    }

    @Test fun `joined borrow uses the same directory and release records numeric census once`() {
        val statistics = N2Statistics()
        val packed = CalleeSubscriptions(f.ops, statistics)
        packed.add(sub(t, listOf(a)))
        packed.add(sub(u, listOf(a)))
        packed.add(sub(t, listOf(b), target = v))
        val observed = ArrayList<Subscription>()
        packed.visitJoinedCandidates(pub(emptyList()), mode, observed::add)
        assertEquals(2, observed.size)
        packed.clear()
        val snapshot = statistics.snapshot()
        assertEquals(2L, snapshot.releasedCallerGroups)
        assertEquals(1L, snapshot.releasedCallerFamilies)
        assertEquals(2L, snapshot.releasedCallerSources)
        assertEquals(2L, snapshot.releasedCallerCells)
        assertEquals(2L, snapshot.releasedCallerDiagonal)
        assertEquals(1L, snapshot.releasedCallerChangingPairs)
        assertEquals(0L, snapshot.releasedCallerScalar)
        assertEquals(0L, snapshot.cumulativeGroups)
        assertTrue(packed.candidates(pub(emptyList()), 0, mode).none())
        packed.clear()
        assertEquals(snapshot, statistics.snapshot(), "Cleared values contribute no second terminal census")
    }
}
