package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.testApManager
import org.opentaint.dataflow.bidi.interp.strongKeep
import org.opentaint.dataflow.bidi.interp.starEdge
import org.opentaint.dataflow.bidi.store.RunSummaryStore
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class FlowSummaryNormalizationTest {
    private val m = testApManager(Cancellation())
    private val ops = ApOps(m)
    private val p = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return
    private val f = m.accessors.index(FieldAccessor("Box", "f", "Box"))
    private val g = m.accessors.index(FieldAccessor("Box", "g", "Box"))
    private val empty = ExclusionSet.Empty
    private val mode = ApMode(false, Direction.FORWARD, 4)
    private fun pattern(base: AccessPathBase = p, path: List<Int> = emptyList(), tail: Tail = Tail.EXACT,
                        e: ExclusionSet = empty, mark: MarkSlot = MarkSlot.STAR) = Pattern(PathFact(base, path, tail, mark), e)
    private fun fact(pattern: Pattern): Facts = m.factsOf(pattern.fact, pattern.exclusion, Layer.NORMAL)
    private fun apply(c: Facts, edge: PathEdge): List<Facts> = CollectingOut().also {
        ops.applyEdge(c, m.initial(pattern()), edge, true, mode, it)
    }.results
    private fun leaves(xs: List<Facts>) = xs.flatMap { ops.leaves(it).toList() }.toSet()

    @Test fun `raw exact FLOW is a read barrier and strong write records the exclusion`() {
        val exact = fact(pattern())
        assertTrue(apply(exact, starEdge(p, listOf(f), ret, emptyList())).isEmpty())
        val written = apply(exact, strongKeep(p, listOf(f)).single()).single() as FlowTree
        assertEquals(Tail.EXACT, written.tail)
        assertEquals(ExclusionSet.of(f), written.exclusion)
        assertEquals(Layer.NORMAL, written.layer)
        val s = normalizeFlowSummary(m, m.initial(pattern()), written)
        assertEquals(Tail.STAR, (s.premise as InitialAp).tail)
        assertEquals(Tail.STAR, (s.facts as FlowTree).tail)
        assertEquals(ExclusionSet.of(f), s.facts.exclusion)
        assertSame(s.premise, normalizeFlowSummary(m, s.premise, s.facts).premise)
        val store = RunSummaryStore(m)
        assertFails { store.add(m.initial(pattern()), written) }
        assertNotNull(store.add(s.premise, s.facts))
    }

    @Test fun `nested write retains outer exclusion and inner ANY demand`() {
        val exact = fact(pattern())
        val outputs = strongKeep(p, listOf(f, g)).flatMap { apply(exact, it) }
        assertEquals(setOf(pattern(e = ExclusionSet.of(f)), pattern(path = listOf(f), tail = Tail.ANY)), leaves(outputs))
        assertEquals(setOf(Layer.NORMAL, Layer.DEMAND), outputs.map { it.layer }.toSet())
        val scalar = strongKeep(p, listOf(f, g)).mapNotNull {
            (concat(Conclusion(pattern().fact, empty, false), it) as? EdgeOutcome.Fact)?.conclusion
        }.map { Pattern(it.fact, it.exclusion) }.toSet()
        assertEquals(leaves(outputs), scalar)
    }

    @Test fun `uniform FLOW query requires a definite uniform actual and preserves its exclusions`() {
        val j = m.initial(pattern(tail = Tail.ANY_TAINT, e = ExclusionSet.of(f)))
        for (tail in listOf(Tail.STAR, Tail.ANY, Tail.EXACT))
            assertNull(ops.satisfying(m.factsOf(pattern(tail = tail).fact, empty,
                if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL), j, mode))
        val uniform = fact(pattern(tail = Tail.ANY_TAINT, e = ExclusionSet.of(f)))
        assertNotNull(ops.satisfying(uniform, j, mode))
        assertNull(ops.satisfying(fact(pattern(tail = Tail.ANY_TAINT, e = ExclusionSet.of(g))), j, mode))
    }

    @Test fun `whole field RemoveAll shares write residuals and rejects below-only all-mark primitive`() {
        val input = fact(pattern())
        val out = CollectingOut()
        ops.clean(input, m.initial(pattern()), Cleaner(p, m.path(listOf(f, g)), CleanReach.AT_AND_BELOW, null), mode, out)
        assertEquals(setOf(pattern(e = ExclusionSet.of(f)), pattern(path = listOf(f), tail = Tail.ANY)), leaves(out.results))
        assertFails { Cleaner(p, null, CleanReach.BELOW, null) }
        assertFails { Cleaner(p, null, CleanReach.EXACT, null) }
    }

    @Test fun `native uniform FLOW views are transient may demands`() {
        for ((input, output) in listOf(Tail.ANY_TAINT to Tail.STAR,
            Tail.ANY_TAINT to Tail.ANY_TAINT, Tail.STAR to Tail.ANY_TAINT)) {
            val j = pattern(tail = input, e = ExclusionSet.of(f))
            val c = pattern(ret, tail = output, e = ExclusionSet.of(g))
            val view = assertNotNull(reverseRecordLeaf(Direction.FORWARD, j, Conclusion(c.fact, c.exclusion, false)))
            assertEquals(Tail.STAR, view.premise.fact.tail)
            assertEquals(ExclusionSet.of(g), view.premise.exclusion)
            assertEquals(Tail.ANY, view.result.fact.tail)
            assertEquals(empty, view.result.exclusion)
            assertTrue(view.result.demand)
        }
    }

    @Test fun `uncertain uniform FLOW transfer loses uniform certainty in every geometry`() {
        val input = fact(pattern(tail = Tail.ANY_TAINT))
        val initial = m.initial(pattern(tail = Tail.ANY_TAINT))
        for (path in listOf(emptyList(), listOf(f))) {
            val edge = starEdge(p, path, ret, emptyList())
            val out = CollectingOut()
            ops.applyEdge(input, initial, edge, true, mode, out, may = true)
            val result = assertIs<FlowTree>(out.results.single())
            assertEquals(Tail.ANY, result.tail)
            assertEquals(Layer.DEMAND, result.layer)
            assertEquals(empty, result.exclusion)
            val reference = assertIs<EdgeOutcome.Fact>(concat(
                Conclusion(pattern(tail = Tail.ANY_TAINT).fact, empty, false), edge, edgeDemand = true))
            assertEquals(ops.leaves(result).single(), Pattern(reference.conclusion.fact, reference.conclusion.exclusion))
        }
    }

    @Test fun `new FLOW point headers keep scalar and packed transfer equal`() {
        for (tail in listOf(Tail.EXACT, Tail.ANY_TAINT))
            for (actualPath in listOf(emptyList(), listOf(f), listOf(f, g)))
                for (fromPath in listOf(emptyList(), listOf(f), listOf(f, g)))
                    for (targetTail in Tail.entries) for (demand in listOf(false, true)) {
                        val input = pattern(path = actualPath, tail = tail)
                        val edge = PathEdge(PathFact(p, fromPath, Tail.STAR, MarkSlot.STAR),
                            PathFact(ret, listOf(g), targetTail, MarkSlot.STAR), ExclusionSet.of(g))
                        val out = CollectingOut()
                        ops.applyEdge(fact(input), m.initial(pattern()), edge, true, mode, out, may = demand)
                        val scalar = concat(Conclusion(input.fact, input.exclusion, false), edge, edgeDemand = demand)
                        val expected = (scalar as? EdgeOutcome.Fact)?.conclusion?.let(::setOf) ?: emptySet()
                        val actual = out.results.flatMap { value -> ops.leaves(value).map {
                            Conclusion(it.fact, it.exclusion, value.layer == Layer.DEMAND)
                        }.toList() }.toSet()
                        assertEquals(expected, actual, "$input / $edge / demand=$demand")
                    }
    }

    @Test fun `concrete STAR summary matches an actual descendant`() {
        val t = MarkSlot.Concrete(m.marks.mark("T"))
        val j = pattern(tail = Tail.STAR, mark = t)
        val a = pattern(path = listOf(f, g), mark = t)
        assertTrue(satisfies(j, a, true))
        assertNotNull(ops.satisfying(fact(a), m.initial(j), mode))
    }
}
