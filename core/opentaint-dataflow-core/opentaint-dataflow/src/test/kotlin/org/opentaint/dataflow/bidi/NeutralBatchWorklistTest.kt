package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class NeutralBatchWorklistTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val v = fixture.mark("V")
    private val field = fixture.field("f")
    private val output = AccessPathBase.Return
    private fun work() = DeltaWorklist(flowFirst = true, batchManager = m)
    private fun delta(mark: TaintMark, node: Int = 1, path: List<Int> = listOf(field),
                      layer: Layer = Layer.DEMAND, protected: Boolean = false): EdgeDelta {
        val initial = m.initial(AccessPathBase.Argument(0), null, Tail.STAR, ExclusionSet.Empty, MarkSlot.Concrete(mark))
        val normalized = m.factsOf(PathFact(output, path, Tail.ANY, MarkSlot.Concrete(mark)),
            ExclusionSet.Empty, Layer.DEMAND) as TaintTree
        // Set the tested header directly: scalar normalization promotes an ANY
        // input to DEMAND before the queue sees it.
        val plain = m.taintTree(output, layer, normalized.root, anyTail = Tail.ANY)
        return EdgeDelta(initial, fixture.inst(node), if (protected) plain.withProtection(plain.root) else plain)
    }
    private fun flow(node: Int = 2): EdgeDelta = EdgeDelta(
        m.initial(AccessPathBase.Argument(0), null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR), fixture.inst(node),
        m.factsOf(PathFact(output, emptyList(), Tail.ANY, MarkSlot.STAR), ExclusionSet.Empty, Layer.DEMAND))
    private fun zero(node: Int = 3) = EdgeDelta(m.zero, fixture.inst(node), Reach.NORMAL)
    private fun mark(delta: EdgeDelta): TaintMark = ((delta.premise as InitialAp).mark as MarkSlot.Concrete).mark

    @Test
    fun `ordinary diagonal marks enqueue one exact cohort`() {
        val queue = work()
        queue.add(delta(t))
        queue.add(delta(u))
        queue.add(delta(v))
        assertEquals(1, queue.size)
        val pending = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(3, pending.batch.size)
        assertEquals(setOf(t, u, v), pending.batch.decode().map { (initial, facts) ->
            val origin = (initial.mark as MarkSlot.Concrete).mark
            assertEquals(setOf(origin), fixture.ops.leaves(facts).map { (it.fact.mark as MarkSlot.Concrete).mark }.toSet())
            origin
        }.toSet())
        assertTrue(queue.isEmpty)
    }

    @Test
    fun `node header field and protection geometry separate pending cohorts`() {
        val queue = work()
        val values = listOf(delta(t), delta(u, node = 2), delta(u, path = emptyList()),
            delta(u, layer = Layer.NORMAL), delta(u, protected = true))
        values.forEach(queue::add)
        assertEquals(values.size, queue.size)
        val batches = List(values.size) { assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch()) }
        assertTrue(batches.all { it.batch.size == 1 })
        assertEquals(1, batches.count { it.batch.template.nonSubsumable != null })
        assertTrue(queue.isEmpty)
    }

    @Test
    fun `pending memberships merge and the same inputs can be queued again after removal`() {
        val queue = work()
        val first = delta(t)
        val last = delta(u)
        listOf(first, last, first.copy()).forEach(queue::add)
        assertEquals(1, queue.size)
        val pending = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(setOf(t, u), pending.batch.decode().map { (it.first.mark as MarkSlot.Concrete).mark }.toSet())
        assertEquals(2, pending.batch.size)
        assertTrue(queue.isEmpty)
        queue.add(first)
        val repeated = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(setOf(t), repeated.batch.decode().map { (it.first.mark as MarkSlot.Concrete).mark }.toSet())
        assertTrue(queue.isEmpty)
    }

    @Test
    fun `pending ZERO disables new cohort admission without losing earlier masks`() {
        val queue = work()
        queue.add(delta(t))
        val control = zero()
        queue.add(control)
        val later = delta(u)
        queue.add(later)
        assertEquals(3, queue.size)
        assertSame(control, assertIs<PendingWork.Scalar>(queue.removeNextBatch()).delta)
        assertSame(later, assertIs<PendingWork.Scalar>(queue.removeNextBatch()).delta)
        val earlier = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(setOf(t), earlier.batch.decode().map { (it.first.mark as MarkSlot.Concrete).mark }.toSet())
        assertTrue(queue.isEmpty)
    }

    @Test
    fun `FLOW work precedes a compact TAINT mask and a returned fallback remainder`() {
        val queue = work()
        listOf(t, u, v).forEach { queue.add(delta(it)) }
        val cohort = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        val first = cohort.batch.take(1)
        assertEquals(1, first.size)
        queue.addBatch(cohort.node, cohort.batch)
        assertFalse(queue.isEmpty)
        assertEquals(1, queue.size)
        val before = flow()
        queue.add(before)
        assertSame(before, assertIs<PendingWork.Scalar>(queue.removeNextBatch()).delta)
        val remainder = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(2, remainder.batch.size)
        assertEquals(setOf(u, v), remainder.batch.decode().map { (it.first.mark as MarkSlot.Concrete).mark }.toSet())
    }

    @Test
    fun `scalar fallback consumes one mark and retains a counted continuation`() {
        val queue = work()
        listOf(t, u, v).forEach { queue.add(delta(it)) }
        val observed = buildSet {
            repeat(3) { index ->
                add(mark(queue.removeNext()))
                assertEquals(index == 2, queue.isEmpty)
            }
        }
        assertEquals(setOf(t, u, v), observed)
        assertEquals(0, queue.size)
    }

    @Test
    fun `clear releases the pending cohort index and the queue together`() {
        val queue = work()
        queue.add(delta(t))
        queue.add(delta(u))
        queue.clear()
        assertTrue(queue.isEmpty)
        assertEquals(0, queue.size)
        queue.add(delta(v))
        val pending = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(setOf(v), pending.batch.decode().map { (it.first.mark as MarkSlot.Concrete).mark }.toSet())
    }

    @Test
    fun `a returned mask joins new pending work without a second scalar archive`() {
        val queue = work()
        queue.add(delta(t))
        queue.add(delta(u))
        val cohort = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(t, (cohort.batch.removeFirst().first.mark as MarkSlot.Concrete).mark)
        queue.add(delta(v))
        queue.addBatch(cohort.node, cohort.batch)
        assertEquals(1, queue.size)
        val remaining = assertIs<PendingWork.MarkedBatch>(queue.removeNextBatch())
        assertEquals(setOf(u, v), remaining.batch.decode().map { (it.first.mark as MarkSlot.Concrete).mark }.toSet())
    }
}
