package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.DeltaWorklist
import org.opentaint.dataflow.bidi.engine.EdgeDelta
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class DeltaWorklistTest {
    private val f = StoreFixtures()
    private val premise = f.manager.initial(f.pattern())
    private fun edge(index: Int, layer: Layer = Layer.NORMAL) = EdgeDelta(premise, f.inst(index), f.fact(layer = layer))
    private fun zero(index: Int, layer: Layer = Layer.NORMAL) = EdgeDelta(f.manager.zero, f.inst(index), f.ops.zero(layer))
    private fun flow(index: Int, layer: Layer = Layer.NORMAL) = EdgeDelta(
        f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR)),
        f.inst(index), f.fact(tail = Tail.STAR, mark = MarkSlot.STAR, layer = layer))

    @Test fun `new worklist has no pending content`() {
        val work = DeltaWorklist()
        assertTrue(work.isEmpty)
        assertFalse(work.hasZeroWork)
        assertEquals(0, work.size)
        assertFails { work.removeNext() }
    }

    @Test fun `ZERO then FLOW then TAINT queues each retain LIFO priority`() {
        val work = DeltaWorklist(flowFirst = true)
        val taintA = edge(1)
        val taintB = edge(2, Layer.DEMAND)
        val flowA = flow(3, Layer.DEMAND)
        val flowB = flow(4)
        val zeroA = zero(5)
        val zeroB = zero(6, Layer.DEMAND)
        listOf(taintA, flowA, zeroA, taintB, flowB, zeroB).forEach(work::add)
        assertEquals(6, work.size)
        for (expected in listOf(zeroB, zeroA)) {
            assertTrue(work.hasZeroWork)
            assertSame(expected, work.removeNext())
        }
        assertFalse(work.hasZeroWork)
        for (expected in listOf(flowB, flowA, taintB, taintA)) assertSame(expected, work.removeNext())
        assertTrue(work.isEmpty)
    }

    @Test fun `default mode keeps FLOW and TAINT in one ordinary LIFO queue`() {
        val work = DeltaWorklist()
        val values = listOf(edge(1), flow(2), edge(3), flow(4))
        values.forEach(work::add)
        assertEquals(values.reversed(), List(values.size) { work.removeNext() })
        assertTrue(work.isEmpty)
    }

    @Test fun `FLOW arriving from TAINT work regains priority without a global barrier`() {
        val work = DeltaWorklist(flowFirst = true)
        val first = edge(1)
        val second = edge(2)
        val generated = flow(3)
        work.add(first)
        work.add(second)
        assertSame(second, work.removeNext())
        work.add(generated)
        assertSame(generated, work.removeNext())
        assertSame(first, work.removeNext())
        assertTrue(work.isEmpty)
    }

    @Test fun `ordinary scalar inputs retain duplicates with no completed-input cache`() {
        val work = DeltaWorklist()
        val first = edge(1)
        val equal = first.copy(facts = f.fact())
        assertEquals(first, equal)
        work.add(first)
        work.add(equal)
        assertEquals(2, work.size)
        assertSame(equal, work.removeNext())
        assertSame(first, work.removeNext())
        assertTrue(work.isEmpty)
        work.add(first)
        assertSame(first, work.removeNext())
        assertTrue(work.isEmpty)
    }

    @Test fun `ordinary equal protection inputs retain their separate annotations`() {
        val work = DeltaWorklist(flowFirst = true)
        val plain = edge(1)
        val facts = plain.facts as TaintTree
        val protected = plain.copy(facts = facts.withProtection(facts.root))
        assertEquals(plain, protected)
        work.add(plain)
        work.add(protected)
        assertEquals(2, work.size)
        assertSame(protected, work.removeNext())
        assertSame(plain, work.removeNext())
        assertTrue(work.isEmpty)
    }

    @Test fun `FLOW field exclusions and excluded marks remain complete queue payloads`() {
        val work = DeltaWorklist(flowFirst = true)
        val flowPremise = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
        val field = f.field("blocked")
        val excludedMark = f.manager.markSetOf(f.mark("U"))
        val inputs = listOf(
            f.fact(tail = Tail.STAR, mark = MarkSlot.STAR),
            f.fact(tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(field)),
            f.fact(tail = Tail.STAR, mark = MarkSlot.Star(excludedMark)),
        ).map { EdgeDelta(flowPremise, f.inst(1), it) }
        inputs.forEach(work::add)
        for (expected in inputs.reversed()) assertSame(expected, work.removeNext())
        assertTrue(work.isEmpty)
    }

    @Test fun `zero priority requires both a zero premise and a REACH conclusion`() {
        val work = DeltaWorklist(flowFirst = true)
        val nonzeroReach = EdgeDelta(premise, f.inst(1), f.ops.zero(Layer.DEMAND))
        val zeroTaint = EdgeDelta(f.manager.zero, f.inst(2), f.fact())
        work.add(nonzeroReach)
        work.add(zeroTaint)
        assertFalse(work.hasZeroWork)
        val normalZero = zero(3)
        val demandZero = zero(4, Layer.DEMAND)
        work.add(normalZero)
        work.add(demandZero)
        assertTrue(work.hasZeroWork)
        assertSame(demandZero, work.removeNext())
        assertTrue(work.hasZeroWork)
        assertSame(normalZero, work.removeNext())
        assertFalse(work.hasZeroWork)
        assertSame(zeroTaint, work.removeNext())
        assertSame(nonzeroReach, work.removeNext())
        assertTrue(work.isEmpty)
    }

    @Test fun `clear releases all priority queues and accepts later work`() {
        val work = DeltaWorklist(flowFirst = true)
        val values = listOf(edge(1), flow(2), zero(3))
        values.forEach(work::add)
        assertEquals(3, work.size)
        assertTrue(work.hasZeroWork)
        work.clear()
        assertTrue(work.isEmpty)
        assertFalse(work.hasZeroWork)
        assertEquals(0, work.size)
        assertFails { work.removeNext() }
        values.forEach(work::add)
        for (expected in values.reversed()) assertSame(expected, work.removeNext())
        assertTrue(work.isEmpty)
    }
}
