package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.starEdge
import org.opentaint.dataflow.bidi.interp.strongKeep
import kotlin.test.*

/** Native transfer checks for the proposed-policy reference counterexample. */
class NestedWriteCycleComponentsTest {
    @Test fun `nested ordinary write promotes an exact FLOW probe to MAY`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0)
        val ff = f.field("f"); val g = f.field("g")
        val initial = f.manager.initial(f.pattern(x, tail = Tail.EXACT, mark = MarkSlot.STAR))
        val actual = f.fact(x, tail = Tail.EXACT, mark = MarkSlot.STAR)
        val out = CollectingOut()
        for (edge in strongKeep(x, listOf(ff, g)))
            f.ops.applyEdge(actual, initial, edge, true, ApMode(false, Direction.FORWARD, 8), out)
        assertEquals(setOf(
            Layer.NORMAL to f.pattern(x, tail = Tail.EXACT, mark = MarkSlot.STAR,
                exclusion = ExclusionSet.of(ff)),
            Layer.DEMAND to f.pattern(x, listOf(ff), Tail.ANY, MarkSlot.STAR)
        ), out.results.flatMap { value -> f.ops.leaves(value).map { value.layer to it }.toList() }.toSet())
        val read = CollectingOut()
        f.ops.applyEdge(actual, initial, starEdge(x, listOf(ff), AccessPathBase.Return, emptyList()),
            true, ApMode(false, Direction.FORWARD, 8), read)
        assertTrue(read.results.isEmpty())
    }

    @Test fun `ordinary read branch carries exact-origin MAY to the return`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0); val y = AccessPathBase.Return
        val ff = f.field("f"); val g = f.field("g")
        val initial = f.manager.initial(f.pattern(x, tail = Tail.EXACT, mark = MarkSlot.STAR))
        var values = listOf(f.fact(x, tail = Tail.EXACT, mark = MarkSlot.STAR))
        fun step(edges: List<PathEdge>) {
            val out = CollectingOut()
            for (value in values) for (edge in edges)
                f.ops.applyEdge(value, initial, edge, true, ApMode(false, Direction.FORWARD, 8), out)
            values = out.results
        }
        step(strongKeep(x, listOf(ff, g)))
        step(listOf(starEdge(x, listOf(ff), y, emptyList())))
        step(strongKeep(y, listOf(ff, g)))
        assertTrue(values.all { it.layer == Layer.DEMAND })
        assertTrue(values.flatMap { f.ops.leaves(it).toList() }.contains(
            f.pattern(y, tail = Tail.ANY, mark = MarkSlot.STAR)))
    }

    @Test fun `the actual g marked input reaches no output in either branch`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0); val y = AccessPathBase.Return
        val ff = f.field("f"); val g = f.field("g")
        val mark = MarkSlot.Concrete(f.mark("T"))
        for (reader in listOf(false, true)) {
            val initial = f.manager.initial(f.pattern(x, listOf(g), Tail.ANY_TAINT, mark))
            var values = listOf(f.fact(x, listOf(g), Tail.ANY_TAINT, mark))
            val stages = listOf(strongKeep(x, listOf(ff, g)),
                listOf(starEdge(x, if (reader) listOf(ff) else emptyList(), y,
                    if (reader) emptyList() else listOf(ff))), strongKeep(y, listOf(ff, g)))
            for (edges in stages) {
                val out = CollectingOut()
                for (value in values) for (edge in edges)
                    f.ops.applyEdge(value, initial, edge, true, ApMode(false, Direction.FORWARD, 8), out)
                values = out.results
            }
            assertTrue(values.isEmpty(), "reader=$reader")
        }
    }

    @Test fun `both known fields remain excluded on an exact writer summary`() {
        val f = StoreFixtures(); val x = AccessPathBase.Argument(0); val y = AccessPathBase.Return
        val ff = f.field("f"); val g = f.field("g")
        val initial = f.manager.initial(f.pattern(x, tail = Tail.EXACT, mark = MarkSlot.STAR))
        var value = f.fact(x, tail = Tail.EXACT, mark = MarkSlot.STAR)
        val path = listOf(strongKeep(x, listOf(ff, g)).first(),
            starEdge(x, emptyList(), y, listOf(ff)), strongKeep(y, listOf(ff, g)).last())
        for (edge in path) {
            val out = CollectingOut()
            f.ops.applyEdge(value, initial, edge, true, ApMode(false, Direction.FORWARD, 8), out)
            value = out.results.single()
        }
        val normal = normalizeFlowSummary(f.manager, initial, value)
        assertEquals(Layer.NORMAL, normal.facts.layer)
        assertEquals(setOf(f.pattern(y, listOf(ff), Tail.STAR, MarkSlot.STAR,
            ExclusionSet.of(intArrayOf(ff, g)))), f.ops.leaves(normal.facts).toSet())
    }
}
