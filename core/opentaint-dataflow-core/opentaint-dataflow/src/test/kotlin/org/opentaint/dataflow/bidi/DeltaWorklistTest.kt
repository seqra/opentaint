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

    @Test fun `nonzero FLOW changed precedes unchanged TAINT`(): Unit {
        val work = DeltaWorklist(flowFirst = true)
        val taintChanged = edge(1)
        val taintUnchanged = edge(2)
        val flowChanged = flow(3, Layer.DEMAND)
        val flowUnchanged = flow(4)
        work.add(taintChanged)
        work.addUnchanged(taintUnchanged)
        work.add(flowChanged)
        work.addUnchanged(flowUnchanged)
        for (expected in listOf(flowUnchanged, flowChanged, taintUnchanged, taintChanged)) {
            assertSame(expected, work.removeNext())
            work.afterProcess()
        }
        assertTrue(work.isEmpty)
    }

    @Test fun `FLOW changed between unchanged partitions retains the repeat burst`(): Unit {
        val work = DeltaWorklist(flowFirst = true)
        val flowUnchanged = flow(1)
        val flowChanged = flow(2)
        val taintUnchanged = edge(3)
        assertTrue(work.addUnchanged(taintUnchanged))
        assertTrue(work.addUnchanged(flowUnchanged))
        work.add(flowChanged)
        assertSame(flowUnchanged, work.removeNext())
        work.afterProcess()
        assertFalse(work.addUnchanged(flowUnchanged))
        assertSame(flowChanged, work.removeNext())
        work.afterProcess()
        assertFalse(work.addUnchanged(flowUnchanged))
        assertFalse(work.addUnchanged(taintUnchanged))
        assertSame(taintUnchanged, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
        assertTrue(work.addUnchanged(flowUnchanged))
        assertTrue(work.addUnchanged(taintUnchanged))
    }

    @Test fun `FLOW arriving from TAINT work regains priority without a global barrier`(): Unit {
        val work = DeltaWorklist(flowFirst = true)
        val first = edge(1)
        val second = edge(2)
        val generated = flow(3)
        work.add(first)
        work.add(second)
        assertSame(second, work.removeNext())
        work.add(generated)
        work.afterProcess()
        assertSame(generated, work.removeNext())
        work.afterProcess()
        assertSame(first, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
    }

    @Test fun `ordinary equal protection upgrade has a distinct unchanged repeat key`(): Unit {
        val work = DeltaWorklist(flowFirst = true)
        val plain = edge(1)
        val facts = plain.facts as TaintTree
        val protected = plain.copy(facts = facts.withProtection(facts.root))
        assertEquals(plain, protected)
        assertTrue(work.addUnchanged(plain))
        assertTrue(work.addUnchanged(protected))
        assertFalse(work.addUnchanged(protected.copy()))
        assertSame(protected, work.removeNext())
        work.afterProcess()
        assertFalse(work.addUnchanged(plain))
        assertSame(plain, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
    }

    @Test fun `clear releases every FLOW priority lane and its shared repeat keys`(): Unit {
        val work = DeltaWorklist(flowFirst = true)
        val changedFlow = flow(1)
        val unchangedFlow = flow(2)
        val changedTaint = edge(3)
        val unchangedTaint = edge(4)
        work.add(changedFlow)
        work.add(changedTaint)
        assertTrue(work.addUnchanged(unchangedFlow))
        assertTrue(work.addUnchanged(unchangedTaint))
        assertEquals(4, work.size)
        work.clear()
        assertTrue(work.isEmpty)
        assertFalse(work.hasZeroWork)
        assertEquals(0, work.size)
        assertFails { work.removeNext() }
        assertTrue(work.addUnchanged(unchangedFlow))
        assertTrue(work.addUnchanged(unchangedTaint))
        assertSame(unchangedFlow, work.removeNext())
        work.afterProcess()
        assertSame(unchangedTaint, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
    }

    @Test fun `new worklist has no pending content`(): Unit {
        val work = DeltaWorklist()
        assertTrue(work.isEmpty)
        assertFalse(work.hasZeroWork)
        assertEquals(0, work.size)
        assertFails { work.removeNext() }
    }

    @Test fun `FLOW priority retains original global unchanged order while ZERO is pending`(): Unit {
        val work = DeltaWorklist(flowFirst = true)
        val changedZero = zero(1)
        val unchangedFlow = flow(2)
        val unchangedZero = zero(3)
        val unchangedTaint = edge(4)
        val changedFlow = flow(5)
        val changedTaint = edge(6)
        work.add(changedTaint)
        work.add(changedFlow)
        work.add(changedZero)
        work.addUnchanged(unchangedFlow)
        work.addUnchanged(unchangedZero)
        work.addUnchanged(unchangedTaint)
        for (expected in listOf(unchangedTaint, unchangedZero, unchangedFlow, changedZero)) {
            assertTrue(work.hasZeroWork)
            assertSame(expected, work.removeNext())
            work.afterProcess()
        }
        assertFalse(work.hasZeroWork)
        assertSame(changedFlow, work.removeNext())
        work.afterProcess()
        assertSame(changedTaint, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
    }

    @Test fun `unchanged then zero then other queues each use LIFO order`(): Unit {
        val work = DeltaWorklist()
        val normalA = edge(1)
        val normalB = edge(2, Layer.DEMAND)
        val zeroA = zero(3)
        val zeroB = zero(4, Layer.DEMAND)
        val unchangedA = edge(5)
        val unchangedB = zero(6)
        work.add(normalA); work.add(normalB); work.add(zeroA); work.add(zeroB)
        assertTrue(work.addUnchanged(unchangedA))
        assertTrue(work.addUnchanged(unchangedB))
        assertEquals(6, work.size)
        for (expected in listOf(unchangedB, unchangedA, zeroB, zeroA, normalB, normalA)) {
            assertSame(expected, work.removeNext())
            work.afterProcess()
        }
        assertTrue(work.isEmpty)
        assertFalse(work.hasZeroWork)
    }

    @Test fun `repeat set lasts through successors and resets after a terminating burst`(): Unit {
        val work = DeltaWorklist()
        val a = edge(1)
        val b = edge(2)
        assertTrue(work.addUnchanged(a))
        assertSame(a, work.removeNext())
        assertFalse(work.addUnchanged(a.copy(facts = f.fact())))
        assertTrue(work.addUnchanged(b))
        work.afterProcess()
        assertFalse(work.addUnchanged(a))
        assertSame(b, work.removeNext())
        assertFalse(work.addUnchanged(b))
        work.afterProcess()
        assertTrue(work.isEmpty)
        assertTrue(work.addUnchanged(a))
        assertSame(a, work.removeNext())
        work.afterProcess()
        assertTrue(work.addUnchanged(a))
    }

    @Test fun `unchanged cycle terminates across one item work quanta`(): Unit {
        val work = DeltaWorklist()
        val nodes = listOf(edge(1), edge(2), edge(3))
        work.addUnchanged(nodes[0])
        val visited = ArrayList<EdgeDelta>()
        repeat(3) { index ->
            assertSame(nodes[index], work.removeNext().also(visited::add))
            assertEquals(index != 2, work.addUnchanged(nodes[(index + 1) % 3]))
            work.afterProcess()
        }
        assertEquals(nodes, visited)
        assertTrue(work.isEmpty)
        assertTrue(work.addUnchanged(nodes[0]))
    }

    @Test fun `unchanged dedup uses complete structural delta content`(): Unit {
        val work = DeltaWorklist()
        val first = edge(1)
        val equal = first.copy(facts = f.fact())
        assertEquals(first, equal)
        assertEquals(first.hashCode(), equal.hashCode())
        assertTrue(work.addUnchanged(first))
        assertFalse(work.addUnchanged(equal))
        val differentPremise = first.copy(premise = f.manager.initial(f.pattern(base = AccessPathBase.Return)))
        val differentNode = first.copy(node = f.inst(2))
        val differentLayer = edge(1, Layer.DEMAND)
        val differentBase = first.copy(facts = f.fact(base = AccessPathBase.Return))
        val differentPath = first.copy(facts = f.fact(path = listOf(f.field("member"))))
        val differentMark = first.copy(facts = f.fact(mark = MarkSlot.Concrete(f.mark("U"))))
        val distinct = listOf(differentPremise, differentNode, differentLayer, differentBase, differentPath, differentMark)
        distinct.forEach { assertTrue(work.addUnchanged(it), "$it") }
        assertEquals(7, work.size)
        assertEquals((listOf(first) + distinct).reversed(), List(7) { work.removeNext() })
        work.afterProcess()
        assertTrue(work.addUnchanged(equal))
    }

    @Test fun `FLOW exclusions and excluded marks are separate repeat keys`(): Unit {
        val work = DeltaWorklist()
        val flowPremise = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
        val field = f.field("blocked")
        val excludedMark = f.manager.markSetOf(f.mark("U"))
        val inputs = listOf(
            f.fact(tail = Tail.STAR, mark = MarkSlot.STAR),
            f.fact(tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(field)),
            f.fact(tail = Tail.STAR, mark = MarkSlot.Star(excludedMark)),
        ).map { EdgeDelta(flowPremise, f.inst(1), it) }
        for (input in inputs) {
            assertTrue(work.addUnchanged(input))
            assertFalse(work.addUnchanged(input.copy()))
        }
        assertEquals(inputs.reversed(), List(3) { work.removeNext() })
        work.afterProcess()
        inputs.forEach { assertTrue(work.addUnchanged(it)) }
    }

    @Test fun `ordinary new deltas retain duplicates and are independent of unchanged repeat keys`(): Unit {
        val work = DeltaWorklist()
        val delta = edge(1)
        work.add(delta)
        work.add(delta.copy(facts = f.fact()))
        assertTrue(work.addUnchanged(delta))
        assertEquals(3, work.size)
        assertSame(delta, work.removeNext())
        work.afterProcess()
        assertTrue(work.addUnchanged(delta))
        assertSame(delta, work.removeNext())
        work.afterProcess()
        assertEquals(delta, work.removeNext())
        work.afterProcess()
        assertSame(delta, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
    }

    @Test fun `zero work counts only pending REACH with a zero premise in either queue`(): Unit {
        val work = DeltaWorklist()
        val nonzeroReach = EdgeDelta(premise, f.inst(1), f.ops.zero(Layer.DEMAND))
        val zeroTaint = EdgeDelta(f.manager.zero, f.inst(2), f.fact())
        work.addUnchanged(nonzeroReach)
        work.addUnchanged(zeroTaint)
        assertFalse(work.hasZeroWork)
        val normalZero = zero(3)
        val unchangedZeroA = zero(4)
        val unchangedZeroB = zero(5, Layer.DEMAND)
        work.add(normalZero)
        assertTrue(work.addUnchanged(unchangedZeroA))
        assertTrue(work.addUnchanged(unchangedZeroB))
        assertFalse(work.addUnchanged(unchangedZeroB.copy()))
        assertEquals(5, work.size)
        assertTrue(work.hasZeroWork)
        assertSame(unchangedZeroB, work.removeNext())
        work.afterProcess()
        assertTrue(work.hasZeroWork)
        assertSame(unchangedZeroA, work.removeNext())
        work.afterProcess()
        assertTrue(work.hasZeroWork)
        assertSame(zeroTaint, work.removeNext())
        work.afterProcess()
        assertSame(nonzeroReach, work.removeNext())
        work.afterProcess()
        assertTrue(work.hasZeroWork)
        assertSame(normalZero, work.removeNext())
        assertFalse(work.hasZeroWork)
        work.afterProcess()
        assertTrue(work.isEmpty)
        assertTrue(work.addUnchanged(unchangedZeroA))
        assertTrue(work.hasZeroWork)
        assertSame(unchangedZeroA, work.removeNext())
        assertFalse(work.hasZeroWork)
        assertFalse(work.addUnchanged(unchangedZeroA))
        work.afterProcess()
        assertTrue(work.addUnchanged(unchangedZeroA))
    }

    @Test fun `clear releases every queue repeat key and zero counter`(): Unit {
        val work = DeltaWorklist()
        val delta = edge(1)
        val zero = zero(2)
        work.add(delta)
        work.add(zero)
        work.addUnchanged(delta)
        work.addUnchanged(zero)
        assertEquals(4, work.size)
        assertTrue(work.hasZeroWork)
        work.clear()
        assertEquals(0, work.size)
        assertTrue(work.isEmpty)
        assertFalse(work.hasZeroWork)
        assertFails { work.removeNext() }
        assertTrue(work.addUnchanged(delta))
        assertTrue(work.addUnchanged(zero))
        assertEquals(2, work.size)
        assertSame(zero, work.removeNext())
        assertFalse(work.hasZeroWork)
        assertSame(delta, work.removeNext())
        work.afterProcess()
        assertTrue(work.isEmpty)
    }
}
