package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.store.PathTrie
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class PathTrieRemovalTest {
    private val base = AccessPathBase.Argument(0)
    @Test fun `remove one exact posting preserves parents siblings and other bases`() {
        val trie = PathTrie<String>()
        val other = AccessPathBase.Argument(1)
        trie.add(base, intArrayOf(), "root")
        trie.add(base, intArrayOf(1, 2), "left")
        trie.add(base, intArrayOf(1, 3), "right")
        trie.add(other, intArrayOf(1, 2), "other")
        assertTrue(trie.remove(base, intArrayOf(1, 2), "left"))
        assertEquals(listOf("root"), trie.lookupPrefixes(base, intArrayOf(1, 2)))
        assertEquals(listOf("right"), trie.lookupExtensions(base, intArrayOf(1)))
        assertEquals(listOf("other"), trie.lookupExtensions(other, intArrayOf()))
        assertFalse(trie.remove(base, intArrayOf(1, 2), "left"))
        assertTrue(trie.remove(base, intArrayOf(), "root"))
        assertTrue(trie.remove(base, intArrayOf(1, 3), "right"))
        assertFalse(trie.isEmpty)
        assertTrue(trie.remove(other, intArrayOf(1, 2), "other"))
        assertTrue(trie.isEmpty)
    }
    @Test fun `equal value at different positions remains independently removable`() {
        val trie = PathTrie<String>()
        trie.add(base, intArrayOf(1), "same")
        trie.add(base, intArrayOf(1, 2), "same")
        assertTrue(trie.remove(base, intArrayOf(1), "same"))
        assertEquals(listOf("same"), trie.lookupExtensions(base, intArrayOf()))
        assertTrue(trie.remove(base, intArrayOf(1, 2), "same"))
        assertTrue(trie.isEmpty)
    }
    @Test fun `deep removal is iterative and cancellation precedes mutation`() {
        val cancellation = Cancellation()
        val trie = PathTrie<String>(cancellation)
        val path = IntArray(32768) { 1 }
        trie.add(base, path, "deep")
        cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { trie.remove(base, path, "deep") }
        cancellation.activate()
        assertEquals(listOf("deep"), trie.lookupExtensions(base, path))
        assertTrue(trie.remove(base, path, "deep"))
        assertTrue(trie.isEmpty)
    }
}
