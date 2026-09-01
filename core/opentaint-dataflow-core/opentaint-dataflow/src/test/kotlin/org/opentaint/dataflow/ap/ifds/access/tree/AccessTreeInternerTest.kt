package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import java.util.concurrent.Callable
import java.util.concurrent.Executors
import java.util.IdentityHashMap
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotEquals
import kotlin.test.assertNotSame
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

class AccessTreeInternerTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = accessor is FieldAccessor
    }

    private fun manager(refManager: RefManager = RefManager()): TreeApManager =
        TreeApManager(UnrollStrategy, refManager, Cancellation())

    private fun node(manager: TreeApManager, field: FieldAccessor): AccessNode = with(manager) {
        create(
            isAbstract = false,
            isFinal = false,
            deepAccessorExclusion = null,
            accessors = intArrayOf(field.idx),
            accessorNodes = arrayOf(finalNode),
        )
    }

    private fun childStorage(node: AccessNode): Any? =
        AccessNode::class.java.getDeclaredField("accessorNodes").run {
            isAccessible = true
            get(node)
        }

    @Test
    fun `storage-local wrappers share one manager canonical node`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")

        val original = node(manager, field)
        val first = AccessTreeSoftInterner(manager).intern(original)
        val second = AccessTreeSoftInterner(manager).intern(node(manager, field))

        assertSame(original, first)
        assertSame(first, second)
    }

    @Test
    fun `small edge storages canonicalize their first write`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val firstStorage = TreeSetWithCompression(1, manager)
        val secondStorage = TreeSetWithCompression(1, manager)

        val first = firstStorage.internIfRequired(node(manager, field))
        val second = secondStorage.internIfRequired(node(manager, field))

        assertSame(first, second)
    }

    @Test
    fun `edge storages recanonicalize nodes from operation-local tables`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val firstLocal = node(manager, field).internNodes(AccessTreeInterner(), IdentityHashMap())
        val secondLocal = node(manager, field).internNodes(AccessTreeInterner(), IdentityHashMap())
        assertNotSame(firstLocal, secondLocal)
        val firstStorage = TreeSetWithCompression(1, manager)
        val secondStorage = TreeSetWithCompression(1, manager)

        val first = firstStorage.internIfRequired(firstLocal)
        val second = secondStorage.internIfRequired(secondLocal)

        assertSame(first, second)
    }

    @Test
    fun `canonical key distinguishes colliding deep exclusions`() {
        val manager = manager()
        val depth0 = DeepAccessorExclusion.create(intArrayOf(0), intArrayOf())!!
        val depth1 = DeepAccessorExclusion.create(intArrayOf(), intArrayOf(900))!!
        assertEquals(depth0.hashCode(), depth1.hashCode())
        val first = with(manager) { create(true, false, depth0, null, null) }
        val second = with(manager) { create(true, false, depth1, null, null) }
        assertEquals(first.hash, second.hash)

        val interner = AccessTreeInterner()
        val canonicalFirst = interner.intern(first)
        val canonicalSecond = interner.intern(second)

        assertNotSame(canonicalFirst, canonicalSecond)
        assertNotEquals(canonicalFirst.deepAccessorExclusion, canonicalSecond.deepAccessorExclusion)
    }

    @Test
    fun `node hash includes accessor labels`() {
        val manager = manager()
        val left = node(manager, FieldAccessor("Box", "left", "String"))
        val right = node(manager, FieldAccessor("Box", "right", "String"))

        assertNotEquals(left.hash, right.hash)
    }

    @Test
    fun `single-child nodes share their accessor array`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val first = node(manager, field)
        val second = node(manager, field)

        assertSame(first.accessors, second.accessors)
    }

    @Test
    fun `child union stores a single child directly`() {
        val manager = manager()
        val node = node(manager, FieldAccessor("Box", "value", "String"))

        assertSame(manager.finalNode, childStorage(node))
        assertSame(manager.finalNode, node.accessorNodeAt(0))
        assertFailsWith<IndexOutOfBoundsException> { node.accessorNodeAt(1) }
    }

    @Test
    fun `child union is null for a node without children`() {
        val manager = manager()

        assertNull(childStorage(manager.finalNode))
    }

    @Test
    fun `child union stores multiple children in an array`() {
        val manager = manager()
        val left = FieldAccessor("Box", "left", "String")
        val right = FieldAccessor("Box", "right", "String")
        val node = with(manager) {
            create(
                isAbstract = false,
                isFinal = false,
                deepAccessorExclusion = null,
                accessors = intArrayOf(left.idx, right.idx),
                accessorNodes = arrayOf(finalNode, abstractNode),
            )
        }

        val storage = childStorage(node)
        assertTrue(storage is Array<*>)
        assertTrue(storage.contentEquals(arrayOf(manager.finalNode, manager.abstractNode)))
        assertSame(manager.finalNode, node.accessorNodeAt(0))
        assertSame(manager.abstractNode, node.accessorNodeAt(1))
    }

    @Test
    fun `access nodes have one child-storage field`() {
        val childStorageFields = AccessNode::class.java.declaredFields.filter {
            it.name == "singleAccessorNode" || it.name == "accessorNodes"
        }

        assertEquals(listOf("accessorNodes"), childStorageFields.map { it.name })
    }

    @Test
    fun `access node metadata uses one packed field`() {
        val fields = AccessNode::class.java.declaredFields.map { it.name }

        assertTrue("state" in fields)
        assertTrue("interned" !in fields)
        assertTrue("isAbstract" !in fields)
        assertTrue("isFinal" !in fields)
        assertTrue("containsStatic" !in fields)
        assertTrue("maxDepth" !in fields)
    }

    @Test
    fun `canonical index drops an old batch at its retention bound`() {
        val manager = manager()
        val interner = AccessTreeInterner(maxEntries = 2)
        val first = node(manager, FieldAccessor("Box", "first", "String"))
        interner.intern(first)
        interner.intern(node(manager, FieldAccessor("Box", "second", "String")))
        interner.intern(node(manager, FieldAccessor("Box", "third", "String")))

        val repeatedFirst = interner.intern(node(manager, FieldAccessor("Box", "first", "String")))

        assertNotSame(first, repeatedFirst)
    }

    @Test
    fun `canonical tables remain isolated between managers`() {
        val firstManager = manager()
        val secondManager = manager()
        val field = FieldAccessor("Box", "value", "String")

        val first = AccessTreeSoftInterner(firstManager).intern(node(firstManager, field))
        val second = AccessTreeSoftInterner(secondManager).intern(node(secondManager, field))

        assertNotSame(first, second)
    }

    @Test
    fun `initial access paths share manager canonical nodes`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val first = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field) as AccessPath
        val second = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field) as AccessPath

        assertSame(first, second)
        assertSame(first.access, second.access)
    }

    @Test
    fun `final facts share manager canonical envelopes`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val first = manager.mostAbstractFinalAp(AccessPathBase.This).prependAccessor(field)
        val second = manager.mostAbstractFinalAp(AccessPathBase.This).prependAccessor(field)

        assertSame(first, second)
    }

    @Test
    fun `initial access path nodes remain isolated between managers`() {
        val firstManager = manager()
        val secondManager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val first = firstManager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field) as AccessPath
        val second = secondManager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field) as AccessPath

        assertNotSame(first.access, second.access)
    }

    @Test
    fun `cleanup preserves live nodes in the manager canonical table`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val wrapper = AccessTreeSoftInterner(manager)
        val beforeCleanup = wrapper.intern(node(manager, field))

        assertEquals(0, manager.refManager.cleanup())
        manager.refManager.enable()
        val afterCleanup = wrapper.intern(node(manager, field))

        assertSame(beforeCleanup, afterCleanup)
    }

    @Test
    fun `concurrent storage wrappers select one canonical node`() {
        val manager = manager()
        val field = FieldAccessor("Box", "value", "String")
        val executor = Executors.newFixedThreadPool(8)
        try {
            val wrappers = List(64) { AccessTreeSoftInterner(manager) }
            val nodes = List(64) { node(manager, field) }
            val tasks = wrappers.zip(nodes).map { (wrapper, node) ->
                Callable {
                    wrapper.intern(node)
                }
            }
            val results = executor.invokeAll(tasks).map { it.get() }

            assertSame(results.first(), results.last())
            assertEquals(1, results.toSet().size)
        } finally {
            executor.shutdownNow()
        }
    }
}
