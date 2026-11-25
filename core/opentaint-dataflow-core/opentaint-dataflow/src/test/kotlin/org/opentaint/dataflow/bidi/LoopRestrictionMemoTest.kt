package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.LoopRestrictionMemo
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.util.RefManager
import org.opentaint.dataflow.util.SoftReferenceManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame

/** P2' (spec/next-iteration-p3-p2m-implementation.md §4.5): the per-run memo of the loop-output
 * restriction computes a key once while it keeps the key, and computes again after each kind of clear. */
class LoopRestrictionMemoTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val x = AccessPathBase.Argument(0)
    private val f = fixture.field("f")
    private val g = fixture.field("g")

    private val key = LoopRestrictionMemo.Key(BlockScope(BlockId(1), PortId(0)), BlockId(2), PortId(3),
        ap.initial(fixture.pattern(x, tail = Tail.STAR, mark = MarkSlot.STAR)), fixture.fact(x, listOf(f)))

    private class Counting {
        var calls = 0
        fun compute(vararg values: Facts): () -> List<Facts> = { calls++; values.toList() }
    }

    @Test fun `equal keys compute once and return the same list`() {
        val memo = LoopRestrictionMemo(SoftReferenceManager(RefManager()))
        val counting = Counting()
        val first = memo.getOrCompute(key, counting.compute(key.value))
        val second = memo.getOrCompute(key.copy(), counting.compute(key.value))
        assertEquals(1, counting.calls)
        assertSame(first, second)
    }

    @Test fun `a change of each key part computes again`() {
        val variants = listOf(
            key.copy(parent = BlockScope(BlockId(1), PortId(1))),
            key.copy(loop = BlockId(4)),
            key.copy(exit = PortId(5)),
            key.copy(original = ap.zero),
            key.copy(value = fixture.fact(x, listOf(g))),
        )
        val memo = LoopRestrictionMemo(SoftReferenceManager(RefManager()))
        val counting = Counting()
        memo.getOrCompute(key, counting.compute(key.value))
        for ((index, variant) in variants.withIndex()) {
            memo.getOrCompute(variant, counting.compute(variant.value))
            assertEquals(index + 2, counting.calls, "variant $index")
        }
        for (variant in listOf(key) + variants) memo.getOrCompute(variant, counting.compute(variant.value))
        assertEquals(variants.size + 1, counting.calls, "every key is kept")
    }

    @Test fun `a full memo clears before it stores`() {
        val memo = LoopRestrictionMemo(SoftReferenceManager(RefManager()), maxEntries = 2)
        val counting = Counting()
        val second = key.copy(loop = BlockId(4))
        val third = key.copy(loop = BlockId(5))
        memo.getOrCompute(key, counting.compute(key.value))
        memo.getOrCompute(second, counting.compute(key.value))
        memo.getOrCompute(third, counting.compute(key.value))
        assertEquals(3, counting.calls)
        memo.getOrCompute(third, counting.compute(key.value))
        assertEquals(3, counting.calls, "the third key is kept")
        memo.getOrCompute(key, counting.compute(key.value))
        assertEquals(4, counting.calls, "the first key went with the clear")
    }

    @Test fun `the memory guard clears the memo and keeps nothing while it is active`() {
        val refs = SoftReferenceManager(RefManager())
        val memo = LoopRestrictionMemo(refs)
        val counting = Counting()
        memo.getOrCompute(key, counting.compute(key.value))
        refs.cleanup()
        memo.getOrCompute(key, counting.compute(key.value))
        memo.getOrCompute(key, counting.compute(key.value))
        assertEquals(3, counting.calls, "a cleared memo and a disabled manager compute every call")
        refs.enable()
        memo.getOrCompute(key, counting.compute(key.value))
        memo.getOrCompute(key, counting.compute(key.value))
        assertEquals(4, counting.calls, "an enabled manager keeps values again")
    }

    @Test fun `clear empties the memo`() {
        val memo = LoopRestrictionMemo(SoftReferenceManager(RefManager()))
        val counting = Counting()
        memo.getOrCompute(key, counting.compute(key.value))
        memo.clear()
        memo.getOrCompute(key, counting.compute(key.value))
        assertEquals(2, counting.calls)
    }
}
