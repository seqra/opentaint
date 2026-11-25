package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.util.Cancellation
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertSame
import kotlin.test.assertTrue

/** P3 (spec/next-iteration-p3-p2m-implementation.md §3.5): the incremental `FlowGroup.addAll` gives the
 * rows and the delta of the native reference for every insertion sequence, and each stored list is a
 * fixpoint (invariant F). Random FLOW packets of one base, both layers, all FLOW tails. */
class FlowGroupIncrementalTest {
    private val fixture = StoreFixtures()
    private val v = StoreValues(fixture)
    private val m = fixture.manager

    private fun randomPath(r: Random, fields: List<Int>): List<Int> = List(r.nextInt(0, 4)) { fields[r.nextInt(fields.size)] }

    private fun randomFlow(r: Random): FlowTree? = with(v) {
        val fields = listOf(f, g, h)
        val layer = if (r.nextBoolean()) Layer.NORMAL else Layer.DEMAND
        val tail = when (r.nextInt(4)) {
            0 -> Tail.STAR; 1 -> Tail.EXACT; 2 -> Tail.ANY_TAINT
            else -> if (layer == Layer.DEMAND) Tail.ANY else Tail.STAR
        }
        val e = if (tail == Tail.ANY) ExclusionSet.Empty
            else ExclusionSet.of(fields.filter { r.nextInt(3) == 0 }.toIntArray())
        val mx = MarkSet(listOf(t, u).filter { r.nextInt(3) == 0 }.map { it.id }.toIntArray())
        val leaves = List(r.nextInt(1, 4)) { leaf(randomPath(r, fields), tail, MarkSlot.Star(mx), layer, e) }
        return try { pack(*leaves.toTypedArray()) as? FlowTree } catch (_: Throwable) { null }
    }

    private fun anyTaint(vararg paths: List<Int>, e: ExclusionSet): FlowTree = with(v) {
        pack(*paths.map { leaf(it, Tail.ANY_TAINT, MarkSlot.Star(MarkSet.EMPTY), Layer.NORMAL, e) }.toTypedArray()) as FlowTree
    }

    private fun layerRows(group: FlowGroup, layer: Layer): List<FlowTree> = group.all().filter { it.layer == layer }.toList()

    /** Runs [values] on the reference and on the landed group, and checks each call. */
    private fun compare(values: List<FlowTree>, label: String, reference: NativeFlowGroupReference = NativeFlowGroupReference(m, m.newInterners().flow)): List<List<FlowTree>> {
        val landed = FlowGroup(m, m.newInterners().flow)
        return values.map { t ->
            val expected = reference.addAll(t)
            val actual = landed.addAll(t)
            assertEquals(expected, actual, "delta, $label")
            assertEquals(reference.all().toList(), landed.all().toList(), "rows, $label")
            for (layer in Layer.entries) {
                assertTrue(reference.isFixpoint(layerRows(landed, layer)), "invariant F, $layer, $label")
            }
            actual
        }
    }

    @Test fun `incremental addAll equals the native reference on random insertion sequences`() {
        var checked = 0
        var nonEmptyDeltas = 0
        var noops = 0
        var mustMerges = 0
        var promotions = 0
        for (seed in 0 until 3000) {
            val r = Random(seed)
            val values = List(r.nextInt(1, 12)) { randomFlow(r) }.filterNotNull()
            val reference = NativeFlowGroupReference(m, m.newInterners().flow)
            for (delta in compare(values, "seed $seed", reference)) {
                if (delta.isEmpty()) noops++ else nonEmptyDeltas++
                checked++
            }
            mustMerges += reference.mustMerges
            promotions += reference.promotions
        }
        assertTrue(checked > 10_000 && nonEmptyDeltas > 1_000 && noops > 1_000,
            "coverage: $checked calls, $nonEmptyDeltas non-empty, $noops empty")
        assertTrue(mustMerges > 0 && promotions > 0, "coverage: $mustMerges MUST merges, $promotions promotions")
    }

    @Test fun `a MUST merge gives the native rows`(): Unit = with(v) {
        val reference = NativeFlowGroupReference(m, m.newInterners().flow)
        compare(listOf(anyTaint(p(f), p(g), e = ex(h)), anyTaint(p(f), e = ex(g))), "MUST merge", reference)
        assertTrue(reference.mustMerges > 0, "the sequence must reach a MUST merge")
    }

    @Test fun `a promotion gives the native rows`(): Unit = with(v) {
        val reference = NativeFlowGroupReference(m, m.newInterners().flow)
        compare(listOf(anyTaint(p(f), e = ex(g, h)), anyTaint(p(f, g), e = ExclusionSet.Empty)), "promotion", reference)
        assertTrue(reference.promotions > 0, "the sequence must reach a promotion")
    }

    @Test fun `a cancelled call keeps the stored rows`() {
        val cancellation = Cancellation()
        val local = StoreFixtures(cancellation)
        with(StoreValues(local)) {
            val group = FlowGroup(local.manager, local.manager.newInterners().flow)
            group.addAll(pack(flow(p(f))) as FlowTree)
            group.addAll(pack(flow(p(g), e = ex(h))) as FlowTree)
            val stored = group.all().toList()
            assertEquals(2, stored.size)
            cancellation.cancel()
            assertFailsWith<Cancellation.Cancelled> { group.addAll(pack(flow(p(h))) as FlowTree) }
            cancellation.activate()
            val after = group.all().toList()
            assertEquals(stored.size, after.size)
            stored.zip(after).forEach { (a, b) -> assertSame(a, b) }
        }
    }
}
