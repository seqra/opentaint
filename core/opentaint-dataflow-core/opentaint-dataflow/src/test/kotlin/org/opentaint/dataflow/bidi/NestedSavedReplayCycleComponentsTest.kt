package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

/** Operators only: the candidate's code has no predefined summaries or pass rules. */
class NestedSavedReplayCycleComponentsTest {
    private class Out : LocalRelationOut {
        val data = arrayListOf<Facts>()
        override fun data(original: PremiseKey, value: Facts) { data += value }
        override fun target(original: PremiseKey, target: Target) = error("No target expected")
        override fun markRequest(mark: TaintMark) = error("No request expected")
    }

    @Test fun `opposite saved reader introduces MAY from wrapper STAR in both directions`() {
        val f = StoreFixtures()
        val field = f.field("f")
        for (direction in listOf(Direction.FORWARD, Direction.BACKWARD)) {
            val from = if (direction == Direction.FORWARD) AccessPathBase.Argument(0) else AccessPathBase.Return
            val to = if (direction == Direction.FORWARD) AccessPathBase.Return else AccessPathBase.Argument(0)
            val initial = f.manager.initial(f.pattern(from, listOf(field), Tail.STAR, MarkSlot.STAR))
            val actual = f.fact(from, listOf(field), Tail.STAR, MarkSlot.STAR)
            val read = f.pattern(from, listOf(field, field), Tail.STAR, MarkSlot.STAR)
            val result = f.pattern(to, tail = Tail.STAR, mark = MarkSlot.STAR)
            val view = RecordLeafView(read, Conclusion(result.fact, result.exclusion, demand = false))
            val app = LocalRelationApplication(f.ops, ApMode(false, direction, 8))
            val out = Out()
            assertTrue(app.applyRecordView(actual, initial, view, false, out))
            assertEquals(Layer.DEMAND, out.data.single().layer)
            assertEquals(f.pattern(to, tail = Tail.ANY, mark = MarkSlot.STAR), f.ops.leaves(out.data.single()).single())
            val nativeInitial = f.manager.initial(read)
            assertFalse(app.applyCurrent(actual, initial, nativeInitial,
                f.fact(to, tail = Tail.STAR, mark = MarkSlot.STAR), Out()))
            assertFalse(app.applyRecord(actual, initial, Record(f.method, direction, nativeInitial,
                f.fact(to, tail = Tail.STAR, mark = MarkSlot.STAR)), Out()))
        }
    }

    @Test fun `the real uniform fg source does not satisfy the saved ff reader`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val ff = f.field("f")
        val g = f.field("g")
        val t = MarkSlot.Concrete(f.mark("T"))
        val actual = f.fact(p, listOf(ff, g), Tail.ANY_TAINT, t)
        val view = RecordLeafView(f.pattern(p, listOf(ff, ff), Tail.STAR, MarkSlot.STAR),
            Conclusion(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR).fact,
                ExclusionSet.Empty, demand = false))
        val out = Out()
        assertFalse(LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8))
            .applyRecordView(actual, f.manager.zero, view, false, out))
        assertTrue(out.data.isEmpty())
    }

    @Test fun `the known ff child has normal service`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val ff = f.field("f")
        val initial = f.manager.initial(f.pattern(p, listOf(ff, ff), Tail.STAR, MarkSlot.STAR))
        val actual = f.fact(p, listOf(ff, ff), Tail.STAR, MarkSlot.STAR)
        val view = RecordLeafView(initial.toPattern(), Conclusion(
            f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR).fact, ExclusionSet.Empty, demand = false))
        val out = Out()
        assertTrue(LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8))
            .applyRecordView(actual, initial, view, false, out))
        assertEquals(Layer.NORMAL, out.data.single().layer)
        assertEquals(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR), f.ops.leaves(out.data.single()).single())
    }
}
