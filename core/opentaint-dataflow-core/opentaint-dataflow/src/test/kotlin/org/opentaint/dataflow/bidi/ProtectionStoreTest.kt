package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import kotlin.test.*

class ProtectionStoreTest {
    private val f = StoreFixtures()
    private val m = f.manager
    private val t = f.mark("T")
    private val u = f.mark("U")
    private fun exact(mark: TaintMark = t, path: List<Int> = emptyList()) =
        f.fact(path = path, mark = MarkSlot.Concrete(mark), layer = Layer.DEMAND) as TaintTree
    private fun any(mark: TaintMark = t) =
        f.fact(tail = Tail.ANY, mark = MarkSlot.Concrete(mark), layer = Layer.DEMAND) as TaintTree
    private fun TaintTree.protected() = withProtection(root)
    private fun group() = TaintGroup(m, m.newInterners().taint)

    @Test fun `equal ordinary membership admits protection once without changing its identity`() {
        val store = group()
        val plain = exact()
        val protected = plain.protected()
        assertEquals(plain, protected)
        assertEquals(plain.hashCode(), protected.hashCode())
        assertNotNull(store.add(plain))
        val upgrade = assertNotNull(store.add(protected))
        assertEquals(plain, upgrade)
        assertEquals(plain.root, upgrade.nonSubsumable)
        assertEquals(plain.root, store.all().single().nonSubsumable)
        assertNull(store.add(protected))
        assertNull(store.add(plain))
    }

    @Test fun `protection merge is sticky in both arrival orders`() {
        val plain = exact()
        for (inputs in listOf(listOf(plain, plain.protected()), listOf(plain.protected(), plain))) {
            val store = group()
            inputs.forEach(store::add)
            val retained = store.all().single()
            assertEquals(plain, retained)
            assertEquals(plain.root, retained.nonSubsumable)
            assertNull(store.add(plain.protected()))
        }
    }

    @Test fun `packed leaf keeps only the selected mark protected`() {
        val store = group()
        val plainT = exact()
        val plainU = exact(u)
        store.add(plainT)
        store.add(plainU)
        val upgrade = assertNotNull(store.add(plainT.protected()))
        assertEquals(m.markSetOf(t), assertNotNull(upgrade.nonSubsumable).leaf.exact)
        val retained = store.all().single()
        assertEquals(m.markSetOf(t) + m.markSetOf(u), retained.root.leaf.exact)
        assertEquals(m.markSetOf(t), assertNotNull(retained.nonSubsumable).leaf.exact)
        assertFalse(u in assertNotNull(retained.nonSubsumable).leaf.exact)
        assertNull(store.add(plainT.protected()))
    }

    @Test fun `protected EXACT remains work under existing plain ANY`() {
        val store = group()
        val field = f.field("child")
        store.add(any())
        store.add(any(u))
        val protected = exact(path = listOf(field)).protected()
        val delta = assertNotNull(store.add(protected))
        assertEquals(protected.root, delta.nonSubsumable)
        assertTrue(store.all().any { it.nonSubsumable == protected.root })
        assertNull(store.add(protected))
        assertTrue(store.all().all { facts ->
            facts.nonSubsumable?.let { !m.taintAlg.foldAll(it).let { leaf -> u in leaf.exact || u in leaf.any } } ?: true
        })
    }

    @Test fun `fresh ordinary mark and protection upgrade are delivered together`() {
        val store = group()
        val plainT = exact()
        val plainU = exact(u)
        store.add(plainT)
        val offered = m.taintTree(plainT.base, plainT.layer,
            m.taintAlg.mergeAdd(plainT.root, plainU.root)).withProtection(plainT.root)
        val delta = assertNotNull(store.add(offered))
        assertEquals(m.markSetOf(t) + m.markSetOf(u), delta.root.leaf.exact)
        assertEquals(plainT.root, delta.nonSubsumable)
        assertNull(store.add(offered))
    }

    @Test fun `layers keep separate protected memberships`() {
        val store = group()
        val demand = exact().protected()
        val normal = demand.withLayer(Layer.NORMAL) as TaintTree
        assertNotNull(store.add(demand))
        assertNotNull(store.add(normal))
        assertEquals(setOf(Layer.NORMAL, Layer.DEMAND), store.all().map { it.layer }.toSet())
        assertTrue(store.all().all { it.nonSubsumable != null })
    }
}
