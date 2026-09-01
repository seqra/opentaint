package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy.AnyAccessorDisabled
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertSame

class RetentionCompressionTest {
    private val manager = TreeApManager(AnyAccessorDisabled, RefManager(), Cancellation())

    @Test
    fun `hybrid set preserves sorted membership across promotion`() {
        val set = HybridIntSet(sparseLimit = 3)
        listOf(9, 2, 5, 2, 12, 1).forEach(set::add)
        val actual = mutableListOf<Int>()

        set.forEach(actual::add)

        assertEquals(listOf(1, 2, 5, 9, 12), actual)
    }

    @Test
    fun `instruction rows allocate only occupied coordinates`() {
        val storage = TestStorage(manager)

        storage.put(19, "right")
        storage.put(3, "left")

        assertContentEquals(intArrayOf(3, 19), storage.keys())
        assertEquals("left", storage.get(3))
        assertEquals("right", storage.get(19))
        assertEquals(null, storage.get(10))
    }

    @Test
    fun `singleton child promotion preserves both children`() {
        val storage = TestChildStorage(manager)
        val first = storage.getOrCreateChild(3)

        assertSame(first, storage.getOrCreateChild(3))
        val second = storage.getOrCreateChild(19)

        assertSame(first, storage.findChild(3))
        assertSame(second, storage.findChild(19))
        assertEquals(null, storage.findChild(10))
    }

    private class TestStorage(manager: TreeApManager) : TreeSetWithCompression(1, manager) {
        fun put(coordinate: Int, value: String) {
            val row = rowsForWrite(coordinate)
            row.values[offsetOf(row, coordinate)] = value
        }

        fun get(coordinate: Int): String? {
            val row = rows() ?: return null
            val offset = offsetOf(row, coordinate)
            return if (offset < 0) null else row.values[offset] as String?
        }

        fun keys(): IntArray = rows()?.keys ?: IntArray(0)
    }

    private class TestChildStorage(manager: TreeApManager) : AccessBasedStorage<TestChildStorage>(manager) {
        override fun createStorage(): TestChildStorage = TestChildStorage(manager)
        override fun printStorageNode(): String = ""
    }
}
