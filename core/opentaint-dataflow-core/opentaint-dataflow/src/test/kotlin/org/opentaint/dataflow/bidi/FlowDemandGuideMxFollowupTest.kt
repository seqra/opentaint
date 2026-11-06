package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.Publication
import org.opentaint.dataflow.bidi.engine.PublicationIndex
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

/** Follow-up only. Exclusions belong to conclusions; the original P is legal FLOW mx{}. */
class FlowDemandGuideMxFollowupTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val x = AccessPathBase.Argument(0)
    private val field = fixture.field("f")
    private val t = fixture.mark("T")
    private val u = fixture.mark("U")
    private val rootPath = emptyList<Int>()
    private val childPath = listOf(field)
    private val original = m.initial(fixture.pattern(AccessPathBase.Return,
        listOf(fixture.field("listener")), Tail.ANY, MarkSlot.STAR))
    private data class Head(val path: List<Int>, val mx: Set<Int>)
    private fun head(path: List<Int>, excluded: TaintMark? = null) =
        Head(path, excluded?.let { setOf(it.id) }.orEmpty())
    private fun flow(path: List<Int>, excluded: List<TaintMark> = emptyList(),
                     layer: Layer = Layer.DEMAND, tail: Tail = Tail.ANY): FlowTree =
        m.flowTree(x, layer, ExclusionSet.Empty, MarkExclusions.of(m.marks, excluded),
            FlowAlgebra.prepend(m, m.path(path), FlowAlgebra.LEAF_NODE), tail)
    private fun heads(values: Iterable<Facts>): Set<Head> = values.flatMap { facts ->
        val value = assertIs<FlowTree>(facts)
        fixture.ops.leaves(value).map { leaf -> Head(leaf.fact.path, value.markExclusion.ids.toSet()) }.toList()
    }.toSet()

    @Test fun `demand guide keeps child mx header in both orders and T2 returns fresh support`() {
        val root = flow(rootPath)
        val childT = flow(childPath, listOf(t))
        for (offers in listOf(listOf(root, childT), listOf(childT, root))) {
            val group = FlowGroup(m, m.newInterners().flow)
            offers.forEach(group::addAll)
            assertEquals(setOf(head(rootPath), head(childPath, t)), heads(group.all().toList()),
                "Ancestor mx{} must not erase the explicit child mx{T} guide head")
            assertTrue(group.addAll(childT).isEmpty(), "Same head and mx are an exact duplicate")

            // The head set is unchanged, but T2's cofinite support grows at f.
            // Returning an exact head difference here would lose this fresh support.
            val fresh = group.addAll(flow(childPath, listOf(u)))
            assertEquals(setOf(head(childPath)), heads(fresh),
                "Same-head mx{T} intersect mx{U} produces a fresh merged mx{} value")
            assertTrue(fresh.any { t !in it.markExclusion && u !in it.markExclusion })
            assertEquals(setOf(head(rootPath), head(childPath)), heads(group.all().toList()))
            assertTrue(group.addAll(flow(childPath, listOf(u))).isEmpty())
        }
    }

    @Test fun `one detached publication batch retains the final child mx replacement`() {
        val index = PublicationIndex(m, fixture.ops)
        val batch = index.addAll(listOf(
            Publication(original, flow(childPath, listOf(t))),
            Publication(original, flow(rootPath, listOf(u))),
            Publication(original, flow(childPath, listOf(u))),
        ))
        batch.forEach { assertSame(original, it.premise, "The original full P stays unchanged") }
        val expected = setOf(head(rootPath, u), head(childPath))
        assertEquals(expected, heads(batch.map { it.conclusion }),
            "retainCurrent must keep the new child mx{} and discard its obsolete mx{T} snapshot")
        val probe = m.factsOf(original.toPattern().fact, original.exclusion, Layer.DEMAND)
        val current = index.candidates(original, probe, ApMode(false, Direction.BACKWARD, 1, MarkMode.FULL))
            .map { it.first }
        current.forEach { assertSame(original, it.premise) }
        assertEquals(expected, heads(current.map { it.conclusion }))
        assertTrue(index.addAll(listOf(Publication(original, flow(childPath, listOf(u))))).isEmpty())
    }

    @Test fun `NORMAL FLOW ANY stays invalid and the factory keeps its demand normalization`() {
        val error = assertFailsWith<IllegalStateException> { flow(childPath, layer = Layer.NORMAL) }
        assertEquals("An ANY FLOW leaf is DEMAND", error.message)
        val normalized = assertIs<FlowTree>(m.factsOf(PathFact(x, childPath, Tail.ANY, MarkSlot.STAR),
            ExclusionSet.Empty, Layer.NORMAL))
        assertEquals(Layer.DEMAND, normalized.layer)
        assertEquals(Tail.ANY, normalized.tail)
    }

    @Test fun `raw DEMAND MUST keeps existing prefix canonicalization in both orders`() {
        val root = flow(rootPath, layer = Layer.DEMAND, tail = Tail.ANY_TAINT)
        val child = flow(childPath, layer = Layer.DEMAND, tail = Tail.ANY_TAINT)
        for (offers in listOf(listOf(root, child), listOf(child, root))) {
            val group = FlowGroup(m, m.newInterners().flow)
            offers.forEach(group::addAll)
            val current = group.all().toList()
            assertEquals(setOf(head(rootPath)), heads(current))
            assertTrue(current.all { it.layer == Layer.DEMAND && it.tail == Tail.ANY_TAINT })
            assertTrue(group.addAll(child).isEmpty())
        }
    }
}
