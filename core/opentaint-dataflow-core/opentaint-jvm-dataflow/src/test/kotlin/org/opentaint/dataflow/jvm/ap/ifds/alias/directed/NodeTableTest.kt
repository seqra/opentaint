package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.test.Test
import kotlin.test.assertContentEquals
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class NodeTableTest {

    private val nodes = NodeTable()

    @Test
    fun `empty set has id 0`() {
        assertEquals(EMPTY_NODE, nodes.intern(intArrayOf()))
        assertEquals(EMPTY_NODE, nodes.of())
        assertContentEquals(intArrayOf(), nodes.members(EMPTY_NODE))
    }

    @Test
    fun `intern gives one id for each set`() {
        val a = nodes.intern(intArrayOf(3, 5, 9))
        val b = nodes.intern(intArrayOf(3, 5, 9))
        val c = nodes.of(9, 3, 5, 3)
        val d = nodes.intern(intArrayOf(3, 5))
        assertEquals(a, b)
        assertEquals(a, c)
        assertNotEquals(a, d)
        assertContentEquals(intArrayOf(3, 5, 9), nodes.members(a))
        assertEquals(a, nodes.find(intArrayOf(3, 5, 9)))
        assertEquals(NO_ID, nodes.find(intArrayOf(4)))
    }

    @Test
    fun `singleton is the node of one origin`() {
        val s = nodes.singleton(7)
        assertEquals(s, nodes.intern(intArrayOf(7)))
        assertEquals(s, nodes.singleton(7))
    }

    @Test
    fun `union is symmetric and memoized`() {
        val a = nodes.of(1, 4)
        val b = nodes.of(2, 4, 8)
        val ab = nodes.union(a, b)
        assertContentEquals(intArrayOf(1, 2, 4, 8), nodes.members(ab))
        val count = nodes.nodeCount
        assertEquals(ab, nodes.union(b, a))
        assertEquals(ab, nodes.union(a, b))
        assertEquals(count, nodes.nodeCount)
        assertEquals(1, nodes.unionMemoSize)

        assertEquals(a, nodes.union(a, a))
        assertEquals(a, nodes.union(a, EMPTY_NODE))
        assertEquals(a, nodes.union(EMPTY_NODE, a))
        assertEquals(1, nodes.unionMemoSize)
    }

    @Test
    fun `union of a subset gives the larger node`() {
        val a = nodes.of(1, 4)
        val b = nodes.of(1, 2, 4)
        assertEquals(b, nodes.union(a, b))
    }

    @Test
    fun `subset and contains`() {
        val a = nodes.of(1, 4)
        val b = nodes.of(1, 2, 4)
        assertTrue(nodes.subset(a, b))
        assertFalse(nodes.subset(b, a))
        assertTrue(nodes.subset(EMPTY_NODE, a))
        assertTrue(nodes.subset(a, a))
        assertTrue(nodes.contains(b, 2))
        assertFalse(nodes.contains(a, 2))
        assertFalse(nodes.contains(EMPTY_NODE, 0))
    }

    @Test
    fun `rename replaces one origin and is memoized`() {
        val a = nodes.of(1, 4, 6)
        val r = nodes.rename(a, 4, 9)
        assertContentEquals(intArrayOf(1, 6, 9), nodes.members(r))
        val count = nodes.nodeCount
        assertEquals(r, nodes.rename(a, 4, 9))
        assertEquals(count, nodes.nodeCount)
        assertEquals(1, nodes.renameMemoSize)

        // The target is already in the set: the two origins merge.
        assertContentEquals(intArrayOf(1, 6), nodes.members(nodes.rename(a, 4, 1)))
        // The origin is not in the set: the node does not change.
        assertEquals(a, nodes.rename(a, 5, 9))
    }

    @Test
    fun `frozen table answers known sets and refuses new sets`() {
        val a = nodes.of(1, 4)
        val b = nodes.of(2)
        val ab = nodes.union(a, b)
        nodes.freeze()
        assertEquals(ab, nodes.union(a, b))
        assertEquals(a, nodes.intern(intArrayOf(1, 4)))
        assertTrue(nodes.subset(a, ab))
        assertFailsWith<IllegalStateException> { nodes.intern(intArrayOf(5)) }
        assertFailsWith<IllegalStateException> { nodes.union(a, nodes.of(3)) }
    }
}
