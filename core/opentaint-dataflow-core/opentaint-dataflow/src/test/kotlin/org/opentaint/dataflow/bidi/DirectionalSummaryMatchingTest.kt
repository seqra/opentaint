package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

class DirectionalSummaryMatchingTest {
    private class Output : LocalRelationOut {
        val data = ArrayList<Facts>()
        val targets = ArrayList<Target>()
        val requests = ArrayList<TaintMark>()
        override fun data(original: PremiseKey, value: Facts) { data += value }
        override fun target(original: PremiseKey, target: Target) { targets += target }
        override fun markRequest(mark: TaintMark) { requests += mark }
    }

    @Test fun `current concrete STAR ancestor cannot satisfy a deeper exact premise in either layer`() {
        val f = StoreFixtures()
        val x = AccessPathBase.Argument(0)
        val field = f.field("f")
        val t = MarkSlot.Concrete(f.mark("T"))
        val initial = f.manager.initial(f.pattern(x, listOf(field), mark = t))
        for (layer in Layer.entries) {
            val actual = f.fact(x, tail = Tail.STAR, mark = t, layer = layer)
            val out = Output()
            assertFalse(LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 4))
                .applyCurrent(actual, initial, initial, f.fact(AccessPathBase.Return, mark = t), out))
            assertTrue(out.data.isEmpty())
        }
    }

    @Test fun `direct saved FLOW STAR ancestor is rejected while at below MAY MUST remain native`() {
        val f = StoreFixtures()
        val x = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val field = f.field("f")
        val g = f.field("g")
        val initial = f.manager.initial(f.pattern(x, listOf(field), Tail.STAR, MarkSlot.STAR))
        val row = Record(f.method, Direction.FORWARD, initial, f.fact(ret, tail = Tail.STAR, mark = MarkSlot.STAR))
        val app = LocalRelationApplication(f.ops, ApMode(false, Direction.FORWARD, 4))
        assertFalse(app.applyRecord(f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR), initial, row, Output()))
        for ((path, tail) in listOf(listOf(field) to Tail.STAR, listOf(field,g) to Tail.STAR,
            emptyList<Int>() to Tail.ANY, emptyList<Int>() to Tail.ANY_TAINT)) {
            val out = Output()
            assertTrue(app.applyRecord(f.fact(x, path, tail, MarkSlot.STAR,
                layer = if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL), initial, row, out))
            assertTrue(out.data.isNotEmpty())
        }
    }

    @Test fun `physical current matcher and target arms reject the same STAR ancestor`() = PipelineFixtures(index = 3).use { f ->
        val field = f.store.field("f")
        val t = MarkSlot.Concrete(f.store.mark("T"))
        val initial = f.ap.initial(f.store.pattern(path = listOf(field), mark = t))
        val actual = f.store.fact(tail = Tail.STAR, mark = t, layer = Layer.DEMAND)
        val pub = Publication(initial, f.store.fact(AccessPathBase.Return, mark = t))
        assertNull(matches(f.subscription(actual), pub, 0, f.ops, f.config.mode))
        val app = LocalRelationApplication(f.ops, f.config.mode)
        assertNull(app.targetArmLayer(actual, initial, Target.DemandTarget, saved = false))
        assertNull(app.targetArmLayer(actual, initial, Target.DemandTarget, saved = true))
    }

    @Test fun `opposite FLOW MUST overlap projects E and keeps full mx through native application`() = PipelineFixtures(index = 2).use { f ->
        val p = AccessPathBase.Argument(0)
        val q = AccessPathBase.Return
        val g = f.store.field("actual excluded")
        val h = f.store.field("writer excluded")
        val t = f.store.mark("T")
        val u = f.store.mark("U")
        val initial = f.ap.initial(f.store.pattern(p, tail = Tail.ANY_TAINT, mark = MarkSlot.STAR))
        val written = f.store.fact(q, tail = Tail.ANY_TAINT,
            mark = MarkSlot.Star(MarkExclusions.of(f.ap.marks, listOf(u))), exclusion = ExclusionSet.of(h))
        f.records.add(Record(f.callee, Direction.FORWARD, initial, written))
        val actual = f.store.fact(q, tail = Tail.STAR,
            mark = MarkSlot.Star(MarkExclusions.of(f.ap.marks, listOf(t))), exclusion = ExclusionSet.of(g))
        f.replayPersisted(f.subscription(actual))
        val selected = f.views.single()
        assertEquals(ExclusionSet.of(intArrayOf(g,h)), (selected.part.added as FlowTree).exclusion)
        val out = CollectingOut()
        f.ops.applyRecordLeaf(selected.part.added, selected.view, selected.nonSubsumable, f.config.mode, out)
        val result = out.results.single()
        assertEquals(Layer.DEMAND, result.layer)
        val leaf = f.ops.leaves(result).single()
        assertEquals(p, leaf.fact.base)
        assertEquals(Tail.ANY, leaf.fact.tail)
        assertEquals(MarkExclusions.of(f.ap.marks,listOf(t,u)), (leaf.fact.mark as MarkSlot.Star).excluded)
        assertTrue(out.markRequests.isEmpty())
    }

    @Test fun `concrete overlap appends protected STAR even when another position already matches`() = PipelineFixtures(index = 2).use { f ->
        val p = AccessPathBase.Argument(0)
        val q = AccessPathBase.Return
        val g = f.store.field("actual excluded")
        val h = f.store.field("writer excluded")
        val k = f.store.field("old matched position")
        val t = MarkSlot.Concrete(f.store.mark("T"))
        val initial = f.ap.initial(f.store.pattern(p, mark = t))
        f.records.add(Record(f.callee, Direction.FORWARD, initial,
            f.store.fact(q, tail = Tail.ANY_TAINT, mark = t, exclusion = ExclusionSet.of(h))))
        val star = f.store.fact(q, tail = Tail.STAR, mark = t, exclusion = ExclusionSet.of(g)) as TaintTree
        val protectedStar = star.withProtection(star.root)
        val exact = f.store.fact(q, listOf(k), mark = t)
        val root = f.ap.taintAlg.mergeAdd(protectedStar.root, (exact as TaintTree).root, f.ap.cancellation)
        val actual = f.ap.taintTree(q, Layer.NORMAL, root, ExclusionSet.of(g), Tail.STAR)
            .withProtection(protectedStar.root)
        f.replayPersisted(f.subscription(actual))
        assertEquals(2, f.views.size, "A legacy packet must not hide a different projected protected STAR contribution")
        val results = f.views.flatMap { selected ->
            CollectingOut().also { f.ops.applyRecordLeaf(selected.part.added, selected.view,
                selected.nonSubsumable, f.config.mode, it) }.results
        }
        assertTrue(results.any { (it as? TaintTree)?.nonSubsumable != null })
        assertTrue(results.all { it.layer == Layer.NORMAL })
    }

    @Test fun `equal view geometry cannot discard MUST conclusion overlap authority`() = PipelineFixtures(index = 2).use { f ->
        val p = AccessPathBase.Argument(0)
        val q = AccessPathBase.Return
        val g = f.store.field("actual excluded")
        val h = f.store.field("writer excluded")
        val initial = f.ap.initial(f.store.pattern(p, tail = Tail.ANY_TAINT, mark = MarkSlot.STAR))
        f.records.add(Record(f.callee, Direction.FORWARD, initial,
            f.store.fact(q, tail = Tail.STAR, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(h))))
        f.records.add(Record(f.callee, Direction.FORWARD, initial,
            f.store.fact(q, tail = Tail.ANY_TAINT, mark = MarkSlot.STAR, exclusion = ExclusionSet.of(h))))
        f.replayPersisted(f.subscription(f.store.fact(q, tail = Tail.STAR, mark = MarkSlot.STAR,
            exclusion = ExclusionSet.of(g))))
        assertEquals(1, f.views.size, "The generic-capability view must not suppress the equal MUST-output view")
    }
}
