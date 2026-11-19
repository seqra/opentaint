package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.strongKeep
import kotlin.test.*

/** Existing native operators used by the exclusion-aware child-cover proof. */
class ExclusionChildReplayNativeTest {
    private class Out : LocalRelationOut {
        val data = arrayListOf<Facts>()
        override fun data(original: PremiseKey, value: Facts) { data += value }
        override fun target(original: PremiseKey, target: Target) = error("No Target expected")
        override fun markRequest(mark: TaintMark) = error("No request expected")
    }

    @Test fun `an excluded first unknown field produces no reply`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
        val field = f.field("f")
        val initial = f.manager.initial(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR))
        val record = RecordLeafView(f.pattern(x, listOf(field), Tail.STAR, MarkSlot.STAR),
            Conclusion(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR).fact, ExclusionSet.Empty, false))
        val out = Out()
        LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8)).applyRecordView(
            f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(field)), initial, record, false, out)
        assertTrue(out.data.isEmpty())
    }

    @Test fun `ordinary parent exclusions do not become child suffix exclusions`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0)
        val ff = f.field("f"); val g = f.field("g"); val h = f.field("h")
        val mode = ApMode(false, Direction.FORWARD, 8)
        fun kept(path: List<Int>): Set<Pattern> {
            val initial = f.manager.initial(f.pattern(x, path, Tail.STAR, MarkSlot.STAR))
            var value = f.fact(x, path, Tail.STAR, MarkSlot.STAR)
            for (written in listOf(g, h)) {
                val out = CollectingOut()
                f.ops.applyEdge(value, initial, strongKeep(x, listOf(written)).single(), true, mode, out)
                value = out.results.single()
            }
            return f.ops.leaves(value).toSet()
        }
        assertEquals(setOf(f.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR,
            exclusion = ExclusionSet.of(intArrayOf(g, h)))), kept(emptyList()))
        assertEquals(setOf(f.pattern(x, listOf(ff), Tail.STAR, MarkSlot.STAR)), kept(listOf(ff)))
    }

    @Test fun `record premise and result exclusions are both respected for real point inputs`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0); val ret = AccessPathBase.Return
        val ff = f.field("f"); val g = f.field("g"); val h = f.field("h")
        val mark = MarkSlot.Concrete(f.mark("T")); val initial = f.manager.zero
        val record = RecordLeafView(f.pattern(x, listOf(ff, ff), Tail.STAR, MarkSlot.STAR, ExclusionSet.of(g)),
            Conclusion(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR).fact, ExclusionSet.of(h), false))
        for (suffix in listOf(emptyList(), listOf(ff), listOf(g), listOf(h))) {
            val out = Out()
            LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8)).applyRecordView(
                f.fact(x, listOf(ff, ff) + suffix, Tail.EXACT, mark), initial, record, false, out)
            if (suffix.firstOrNull() in setOf(g, h)) assertTrue(out.data.isEmpty())
            else {
                assertEquals(setOf(f.pattern(ret, suffix, Tail.EXACT, mark)),
                    out.data.flatMap { f.ops.leaves(it).toList() }.toSet())
                assertTrue(out.data.all { it.layer == Layer.NORMAL })
            }
        }
    }
}
