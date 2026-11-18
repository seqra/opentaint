package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.strongKeep
import org.opentaint.dataflow.bidi.interp.starEdge
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

/** Native operators for ordinary writes; no cleaner or predefined-summary rule. */
class OverwriteSavedReplayCycleComponentsTest {
    private class Out : LocalRelationOut {
        val data = arrayListOf<Facts>()
        override fun data(original: PremiseKey, value: Facts) { data += value }
        override fun target(original: PremiseKey, target: Target) = error("No Target expected")
        override fun markRequest(mark: TaintMark) = error("No mark request expected")
    }

    @Test fun `ordinary pre and post writes leave g excluded on both NORMAL relations`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
        val ff = f.field("f"); val g = f.field("g"); val mode = ApMode(false, Direction.FORWARD, 8)
        for (reader in listOf(false, true)) for (tail in listOf(Tail.EXACT, Tail.STAR)) {
            val path = if (reader) listOf(ff, ff) else emptyList()
            val initial = f.manager.initial(f.pattern(x, path, tail, MarkSlot.STAR))
            var value = f.fact(x, path, tail, MarkSlot.STAR)
            fun apply(edge: PathEdge) {
                val out = CollectingOut()
                f.ops.applyEdge(value, initial, edge, true, mode, out)
                value = out.results.single()
            }
            apply(strongKeep(x, listOf(g)).single())
            apply(starEdge(x, if (reader) listOf(ff, ff) else emptyList(), ret,
                if (reader) emptyList() else listOf(ff, ff)))
            apply(strongKeep(ret, listOf(g)).single())
            val normal = normalizeFlowSummary(f.manager, initial, value)
            assertEquals(Layer.NORMAL, normal.facts.layer)
            assertEquals(Tail.STAR, (normal.premise as InitialAp).tail)
            assertEquals(setOf(f.pattern(ret, if (reader) emptyList() else listOf(ff, ff),
                Tail.STAR, MarkSlot.STAR, ExclusionSet.of(g))), f.ops.leaves(normal.facts).toSet())
        }
    }

    @Test fun `opposite excluded NORMAL reader creates coarse MAY in either direction`() {
        val f = StoreFixtures(); val ff = f.field("f"); val g = f.field("g")
        for (direction in listOf(Direction.FORWARD, Direction.BACKWARD)) {
            val from = if (direction == Direction.FORWARD) AccessPathBase.Argument(0) else AccessPathBase.Return
            val to = if (direction == Direction.FORWARD) AccessPathBase.Return else AccessPathBase.Argument(0)
            val original = f.manager.initial(f.pattern(from, listOf(ff), Tail.STAR, MarkSlot.STAR))
            val view = RecordLeafView(f.pattern(from, listOf(ff, ff), Tail.STAR, MarkSlot.STAR),
                Conclusion(f.pattern(to, tail = Tail.STAR, mark = MarkSlot.STAR).fact, ExclusionSet.of(g), false))
            val out = Out()
            assertTrue(LocalRelationApplication(f.ops, ApMode(false, direction, 8)).applyRecordView(
                f.fact(from, listOf(ff), Tail.STAR, MarkSlot.STAR), original, view, false, out))
            assertEquals(Layer.DEMAND, out.data.single().layer)
            assertEquals(setOf(f.pattern(to, tail = Tail.ANY, mark = MarkSlot.STAR)),
                f.ops.leaves(out.data.single()).toSet())
        }
    }

    @Test fun `native reversal keeps g excluded on the opposite NORMAL view`() {
        val f = StoreFixtures(); val ff = f.field("f"); val g = f.field("g")
        val p = f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = MarkSlot.STAR)
        val c = f.pattern(AccessPathBase.Return, listOf(ff, ff), Tail.STAR, MarkSlot.STAR, ExclusionSet.of(g))
        val reverse = assertNotNull(reverseRecordLeaf(Direction.FORWARD, p, Conclusion(c.fact, c.exclusion, false)))
        assertEquals(f.pattern(AccessPathBase.Return, listOf(ff, ff), Tail.STAR, MarkSlot.STAR), reverse.premise)
        assertEquals(p.fact, reverse.result.fact)
        assertEquals(ExclusionSet.of(g), reverse.result.exclusion)
        assertFalse(reverse.result.demand)
    }

    @Test fun `real fg uniform input uses writer normally and does not match reader`() {
        val f = StoreFixtures(); val ff = f.field("f"); val g = f.field("g")
        val x = AccessPathBase.Argument(0); val ret = AccessPathBase.Return; val mark = MarkSlot.Concrete(f.mark("T"))
        val actual = f.fact(x, listOf(ff, g), Tail.ANY_TAINT, mark)
        val initial = f.manager.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
        val out = Out(); val mode = ApMode(false, Direction.FORWARD, 8)
        assertTrue(LocalRelationApplication(f.ops, mode).applyRecord(actual, f.manager.zero,
            Record(f.method, Direction.FORWARD, initial,
                f.fact(ret, listOf(ff, ff), Tail.STAR, MarkSlot.STAR, ExclusionSet.of(g))), out))
        assertEquals(setOf(f.pattern(ret, listOf(ff, ff, ff, g), Tail.ANY_TAINT, mark)),
            f.ops.leaves(out.data.single()).toSet())
        assertEquals(Layer.NORMAL, out.data.single().layer)
        val reader = RecordLeafView(f.pattern(x, listOf(ff, ff), Tail.STAR, MarkSlot.STAR),
            Conclusion(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR).fact, ExclusionSet.of(g), false))
        assertFalse(LocalRelationApplication(f.ops, mode).applyRecordView(actual, f.manager.zero, reader, false, Out()))
    }
}
