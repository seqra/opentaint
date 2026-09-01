package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import java.util.IdentityHashMap
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame

class AccessTreeAnySuffixMatcherTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = accessor is FieldAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())

    @Test
    fun `shared fallback subtree is evaluated once`() {
        val left = FieldAccessor("Box", "left", "Box")
        val right = FieldAccessor("Box", "right", "Box")
        val suffix = FieldAccessor("Box", "suffix", "Box")
        val suffixNode = with(manager) {
            create(false, false, null, intArrayOf(suffix.idx), arrayOf(finalNode))
        }
        val candidate = with(manager) {
            create(false, false, null, intArrayOf(left.idx, right.idx), arrayOf(finalNode, finalNode))
        }
        val matcher = AccessTreeAnySuffixMatcher(suffixNode)

        assertSame(candidate, matcher.getNonMatchingNode(candidate))

        val memo = AccessTreeAnySuffixMatcher::class.java.getDeclaredField("memoCovered").run {
            isAccessible = true
            @Suppress("UNCHECKED_CAST")
            get(matcher) as IdentityHashMap<Any, IdentityHashMap<Any, Any>>
        }
        assertEquals(2, memo.values.sumOf { it.size })
    }
}
