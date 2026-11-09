package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Finalized spec 2.1: plain and protected are independent logical memberships. */
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

    @Test fun `identity and freshness include the protection class in both orders`() {
        val plain = exact()
        val protected = plain.protected()
        assertNotEquals(plain, protected)
        assertNotEquals(plain.groupKey, protected.groupKey)
        for (inputs in listOf(listOf(plain, protected), listOf(protected, plain))) {
            val store = group()
            for (value in inputs) assertEquals(listOf(value), store.addAll(value))
            assertEquals(setOf(plain, protected), store.all().toSet())
            for (value in inputs) assertTrue(store.addAll(value).isEmpty())
        }
    }

    @Test fun `packed leaf stores both classes without upgrading another mark`() {
        val store = group()
        val plainT = exact()
        val plainU = exact(u)
        store.addAll(plainT)
        store.addAll(plainU)
        assertEquals(listOf(plainT.protected()), store.addAll(plainT.protected()))
        val retained = store.all().toList()
        assertEquals(2, retained.size)
        val plain = retained.single { it.nonSubsumable == null }
        assertEquals(m.markSetOf(t) + m.markSetOf(u), plain.root.leaf.exact)
        val protected = retained.single { it.nonSubsumable != null }
        assertEquals(m.markSetOf(t), protected.root.leaf.exact)
        assertEquals(protected.root, protected.nonSubsumable)
    }

    @Test fun `different classes never cover each other in either arrival order`() {
        val child = exact(path = listOf(f.field("child")))
        for (inputs in listOf(listOf(any().protected(), child), listOf(child, any().protected()))) {
            val store = group()
            inputs.forEach { store.addAll(it) }
            assertEquals(inputs.toSet(), store.all().toSet())
        }
        val store = group()
        store.addAll(any())
        store.addAll(child.protected())
        assertTrue(store.addAll(child).isEmpty())
        assertEquals(setOf(any(), child.protected()), store.all().toSet())
    }

    @Test fun `fresh mixed producer splits exact coordinates before class admission`() {
        val plainT = exact()
        val plainU = exact(u)
        val mixed = m.taintTree(plainT.base, plainT.layer,
            m.taintAlg.mergeAdd(plainT.root, plainU.root)).withProtection(plainT.root)
        val store = group()
        assertEquals(setOf(plainT.protected(), plainU), store.addAll(mixed).toSet())
        assertEquals(setOf(plainT.protected(), plainU), store.all().toSet())
        assertTrue(store.addAll(mixed).isEmpty())
    }

    @Test fun `scalar identity promotion restores both classes`() {
        val initial = m.initial(f.pattern(tail = Tail.EXACT))
        val value = f.ops.startFact(initial) as TaintTree
        for (packed in listOf(false, true)) {
            val store = MethodEdgeStore(m, f.method, f.lm, 3, flowBacked = packed)
            assertEquals(listOf(value), store.addAll(f.inst(1), initial, value))
            assertEquals(listOf(value.protected()), store.addAll(f.inst(1), initial, value.protected()))
            val different = exact(path = listOf(f.field("child"))).withLayer(value.layer)
            store.addAll(f.inst(1), initial, different)
            val stored = store.edgesAt(f.inst(1), initial).map { it.second }.toList()
            assertTrue(stored.any { it is TaintTree && it.nonSubsumable == null && !it.root.leaf.exact.isEmpty })
            assertTrue(stored.any { it is TaintTree && it.nonSubsumable != null && !it.root.leaf.exact.isEmpty })
            assertTrue(store.addAll(f.inst(1), initial, value).isEmpty())
            assertTrue(store.addAll(f.inst(1), initial, value.protected()).isEmpty())
        }
    }

    @Test fun `layers and flags remain independent`() {
        val store = group()
        for (layer in Layer.entries) for (protected in listOf(false, true)) {
            val value = exact().withLayer(layer) as TaintTree
            assertEquals(1, store.addAll(if (protected) value.protected() else value).size)
        }
        assertEquals(4, store.all().count())
    }
}
