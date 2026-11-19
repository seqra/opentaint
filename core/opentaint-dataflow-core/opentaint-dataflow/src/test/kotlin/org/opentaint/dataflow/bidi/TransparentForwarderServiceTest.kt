package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

/** Native service of the proposed owner projection. No owner-routing or NE
 * production change is installed by these component tests. */
class TransparentForwarderServiceTest {
    private class Output : LocalRelationOut {
        val data = arrayListOf<Facts>()
        override fun data(original: PremiseKey, value: Facts) { data += value }
        override fun target(original: PremiseKey, target: Target) = error("Unexpected target")
        override fun markRequest(mark: TaintMark) = error("Unexpected request")
    }

    @Test fun `original marked inputs cross three canonical calls without a MAY result`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val field = f.field("f")
        val g = f.field("g")
        val t = MarkSlot.Concrete(f.mark("T"))
        val write = Record(f.method, Direction.FORWARD,
            f.manager.initial(f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR)),
            f.fact(ret, listOf(field, field), Tail.STAR, MarkSlot.STAR))
        val read = RecordLeafView(f.pattern(p, listOf(field, field), Tail.STAR, MarkSlot.STAR),
            Conclusion(f.pattern(ret, tail = Tail.STAR, mark = MarkSlot.STAR).fact,
                ExclusionSet.Empty, demand = false))
        val app = LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8))
        var actuals = listOf(f.fact(p, listOf(field, g), Tail.ANY_TAINT, t))
        repeat(3) {
            val out = Output()
            for (actual in actuals) {
                app.applyRecord(actual, f.manager.zero, write, out)
                app.applyRecordView(actual, f.manager.zero, read, false, out)
            }
            assertTrue(out.data.all { value -> value.layer == Layer.NORMAL })
            val leaves = out.data.flatMap { f.ops.leaves(it).toList() }.distinct()
            assertTrue(leaves.all { it.fact.tail == Tail.ANY_TAINT && it.fact.mark == t })
            actuals = leaves.map { leaf ->
                f.manager.factsOf(leaf.fact.copy(base = p), leaf.exclusion, Layer.NORMAL)
            }
        }
        assertEquals(setOf(List(3) { field } + g, List(7) { field } + g),
            actuals.flatMap { f.ops.leaves(it).map { p -> p.fact.path } }.toSet())
    }

    @Test fun `canonical NORMAL service preserves a DEMAND input layer`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val field = f.field("f")
        val g = f.field("g")
        val t = MarkSlot.Concrete(f.mark("T"))
        val record = Record(f.method, Direction.FORWARD,
            f.manager.initial(f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR)),
            f.fact(ret, listOf(field, field), Tail.STAR, MarkSlot.STAR))
        val out = Output()
        assertTrue(LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 8)).applyRecord(
            f.fact(p, listOf(field, g), Tail.ANY_TAINT, t, layer = Layer.DEMAND),
            f.manager.zero, record, out))
        assertTrue(out.data.isNotEmpty())
        assertTrue(out.data.all { it.layer == Layer.DEMAND })
    }

    @Test fun `backward canonical replay keeps the real producer route`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val field = f.field("f")
        val t = MarkSlot.Concrete(f.mark("T"))
        val view = RecordLeafView(f.pattern(ret, listOf(field, field), Tail.STAR, MarkSlot.STAR),
            Conclusion(f.pattern(p, tail = Tail.STAR, mark = MarkSlot.STAR).fact,
                ExclusionSet.Empty, demand = false))
        val app = LocalRelationApplication(f.ops, ApMode(false, Direction.BACKWARD, 7))
        var actual = f.fact(ret, tail = Tail.ANY, mark = t, layer = Layer.DEMAND)
        repeat(3) {
            val out = Output()
            assertTrue(app.applyRecordView(actual, f.manager.zero, view, false, out))
            val value = out.data.single()
            assertEquals(Layer.DEMAND, value.layer)
            val leaf = f.ops.leaves(value).single()
            assertEquals(f.pattern(p, tail = Tail.ANY, mark = t), leaf)
            actual = f.manager.factsOf(leaf.fact.copy(base = ret), leaf.exclusion, value.layer)
        }
    }
}
