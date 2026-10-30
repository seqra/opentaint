package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.MethodEdgeStore
import kotlin.test.*

class MethodIdentityStorageTest {
    private val fixture = StoreFixtures()
    private val m = fixture.manager
    private val v = StoreValues(fixture)

    private data class Annotated(val facts: Facts, val mask: TaintNode?)
    private fun annotated(facts: Facts?) = facts?.let { Annotated(it, (it as? TaintTree)?.nonSubsumable) }
    private fun annotated(facts: Sequence<Facts>) = facts.map { annotated(it)!! }.toSet()

    @Test
    fun `identity admission matches scalar group state and every delta for all layers and protection orders`(): Unit = with(v) {
        for (tail in Tail.entries) for (flow in listOf(false, true)) {
            val key = premise(p(f, g), tail, if (flow) MarkSlot.STAR else mt)
            val initials = Layer.entries.filter { !(flow && tail == Tail.ANY && it == Layer.NORMAL) }.map {
                initialImage(m, key, it, false)
            }
            val choices = initials + initials.filterIsInstance<TaintTree>().map { it.withProtection(it.root) }
            // Exhaust every event sequence of length three: plain repeats and late protection upgrades.
            for (a in choices) for (b in choices) for (c in choices) {
                val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2, collectStatistics = true)
                val reference = ConclusionGroup(m, m.newInterners())
                val node = fixture.inst(1)
                for (offered in listOf(a, b, c, a)) {
                    assertEquals(annotated(reference.add(offered)), annotated(store.add(node, key, offered)))
                    assertEquals(annotated(reference.all()), annotated(store.edgesAt(node, key).map { it.second }))
                }
                assertTrue(store.edgesAt(fixture.inst(2), key).none())
            }
        }
    }

    @Test
    fun `competing value promotes only its own producer without reemitting the restored identity`(): Unit = with(v) {
        for (flow in listOf(false, true)) for (firstLayer in Layer.entries) {
            val key = premise(p(f), Tail.STAR, if (flow) MarkSlot.STAR else mt, ex(h))
            val plain = initialImage(m, key, firstLayer, false)
            val original = if (plain is TaintTree) plain.withProtection(plain.root) else plain
            val competing = if (flow) listOf(
                pack(leaf(p(f), Tail.ANY, MarkSlot.STAR, Layer.DEMAND)),
                pack(leaf(p(f), Tail.STAR, MarkSlot.STAR, firstLayer, ex(g))),
                pack(leaf(p(g), Tail.STAR, MarkSlot.STAR, firstLayer, ex(h))),
                pack(leaf(p(f), Tail.STAR, MarkSlot.Star(marks(t.id)), firstLayer, ex(h))),
                pack(leaf(p(f), Tail.STAR, MarkSlot.STAR, firstLayer, ex(h), y)),
            ) else listOf(
                pack(leaf(p(f), Tail.ANY, mt, Layer.DEMAND)),
                pack(leaf(p(f), Tail.STAR, mt, firstLayer, ex(g))),
                pack(leaf(p(g), Tail.STAR, mu, firstLayer, ex(h))),
                pack(leaf(p(f), Tail.STAR, mt, firstLayer, ex(h), y)),
                pack(leaf(p(f), Tail.STAR, mt, firstLayer, ex(h)),
                    leaf(p(g), Tail.STAR, mu, firstLayer, ex(h))),
            )
            for (other in competing) {
                val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2, collectStatistics = true)
                val reference = ConclusionGroup(m, m.newInterners())
                val node = fixture.inst(1)
                val untouched = fixture.inst(2)
                store.add(untouched, key, original)
                for (offered in listOf(original, original.withLayer(
                    if (firstLayer == Layer.NORMAL) Layer.DEMAND else Layer.NORMAL), other, original, other)) {
                    assertEquals(annotated(reference.add(offered)), annotated(store.add(node, key, offered)))
                    assertEquals(annotated(reference.all()), annotated(store.edgesAt(node, key).map { it.second }))
                }
                assertEquals(setOf(annotated(original)), annotated(store.edgesAt(untouched, key).map { it.second }))
                val statistics = assertNotNull(store.scalarStatisticsSnapshot())
                assertEquals(1L, statistics.fullPoints)
                assertEquals(1L, statistics.compactNormal + statistics.compactDemand)
            }
        }
    }

    @Test
    fun `whole stored images remain queryable and unsupported multi-premises stay full`(): Unit = with(v) {
        val key = premise(p(f), Tail.STAR, mt)
        val identity = initialImage(m, key, Layer.NORMAL, false)
        val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2, collectStatistics = true)
        val node = fixture.inst(1)
        store.add(node, key, identity)
        val query = fixture.pattern(path = p(f), tail = Tail.STAR)
        assertEquals(setOf(key to identity), store.edgesAt(node, query).toSet())
        assertTrue(store.edgesAt(node, fixture.pattern(path = p(g))).none())
        val nd = nd()
        store.add(node, nd, identity)
        assertEquals(setOf(key to identity, nd to identity), store.edgesAt(node).toSet())
        val statistics = assertNotNull(store.scalarStatisticsSnapshot())
        assertEquals(1L, statistics.compactNormal)
        assertEquals(1L, statistics.fullPoints)
    }

    @Test
    fun `compact plain and protected states match an independent finite membership model`(): Unit = with(v) {
        val key = premise(p(f), Tail.EXACT, mt)
        val plain = initialImage(m, key, Layer.NORMAL, false) as TaintTree
        val guarded = plain.withProtection(plain.root)
        for (events in 0 until 64) {
            val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2)
            var present = false
            var protected = false
            for (step in 0 until 6) {
                val offeredProtected = events and (1 shl step) != 0
                val offered = if (offeredProtected) guarded else plain
                val fresh = !present || (offeredProtected && !protected)
                val delta = store.add(fixture.inst(1), key, offered)
                assertEquals(fresh, delta != null)
                if (fresh) assertEquals(annotated(offered), annotated(delta))
                present = true
                protected = protected || offeredProtected
                val stored = store.edgesAt(fixture.inst(1), key).single().second as TaintTree
                assertEquals(plain, stored)
                assertEquals(if (protected) plain.root else null, stored.nonSubsumable)
            }
        }
    }

    @Test
    fun `unique compact points count layer overlap once without changing layer membership gauges`(): Unit = with(v) {
        val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2, collectStatistics = true)
        assertEquals(0L, assertNotNull(store.scalarStatisticsSnapshot()).compactPoints)
        val key = premise(p(f), Tail.STAR, mt)
        val normal = initialImage(m, key, Layer.NORMAL, false)
        val demand = initialImage(m, key, Layer.DEMAND, false)
        store.add(fixture.inst(1), key, normal)
        store.add(fixture.inst(1), key, demand)
        store.add(fixture.inst(2), key, normal)
        store.add(fixture.inst(3), key, demand)
        val both = assertNotNull(store.scalarStatisticsSnapshot())
        assertEquals(3L, both.compactPoints)
        assertEquals(2L, both.compactNormal)
        assertEquals(2L, both.compactDemand)
        assertEquals(4L, both.compactTaint)
        // Promoting the shared point removes one cell and both layer memberships.
        store.add(fixture.inst(1), key, pack(leaf(p(g))))
        val promoted = assertNotNull(store.scalarStatisticsSnapshot())
        assertEquals(2L, promoted.compactPoints)
        assertEquals(1L, promoted.compactNormal)
        assertEquals(1L, promoted.compactDemand)
        assertEquals(1L, promoted.fullPoints)
    }

    @Test
    fun `statistics disabled path remains absent before and after admissions`(): Unit = with(v) {
        val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2)
        assertNull(store.scalarStatisticsSnapshot())
        val key = premise(p(f), Tail.STAR, mt)
        store.add(fixture.inst(1), key, initialImage(m, key, Layer.NORMAL, false))
        assertNull(store.scalarStatisticsSnapshot())
        store.add(fixture.inst(1), key, pack(leaf(p(g))))
        assertNull(store.scalarStatisticsSnapshot())
    }

    @Test
    fun `packed path and reach bits retain their current storage and delta behavior`(): Unit = with(v) {
        val key = premise(p(f), Tail.STAR, mt)
        val store = MethodEdgeStore(m, fixture.method, fixture.lm, 2, flowBacked = true, collectStatistics = true)
        val node = fixture.inst(1)
        val identity = initialImage(m, key, Layer.NORMAL, false)
        assertNotNull(store.add(node, key, identity))
        assertNull(store.add(node, key, identity))
        assertSame(Reach.NORMAL, store.add(node, key, Reach.NORMAL))
        assertNull(store.add(node, key, Reach.NORMAL))
        assertEquals(setOf(key to identity, key to Reach.NORMAL), store.edgesAt(node).toSet())
        assertEquals(0L, assertNotNull(store.scalarStatisticsSnapshot()).compactNormal)
    }
}
