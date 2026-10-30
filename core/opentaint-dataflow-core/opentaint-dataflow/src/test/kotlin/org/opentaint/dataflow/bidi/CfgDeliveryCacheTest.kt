package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.engine.CfgDeliveryCache
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet
import kotlin.test.*

class CfgDeliveryCacheTest {
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private fun graph(next: List<List<Int>>) = CompactGraph.build(next.size) { n ->
        BitSet().apply { next[n].forEach(::set) }
    }

    @Test fun `all three-node CFGs agree with independent neutral closure for each start and relevance mask`() {
        val cancellation = Cancellation()
        // Exhaustive includes diamonds, dead ends, cycles and relevant identity loops.
        for (edges in 0 until (1 shl 9)) {
            val next = List(3) { n -> (0..2).filter { edges and (1 shl (3 * n + it)) != 0 } }
            for (mask in 0 until 8) {
                var evaluations = 0
                val cache = CfgDeliveryCache(graph(next), cancellation) { node, _ ->
                    evaluations++; mask and (1 shl node) != 0
                }
                for (start in 0..2) {
                    val reached = mutableSetOf(start)
                    var changed: Boolean
                    do {
                        changed = false
                        for (node in reached.toList()) if (mask and (1 shl node) == 0)
                            for (target in next[node]) if (reached.add(target)) changed = true
                    } while (changed)
                    val expected = reached.filter { mask and (1 shl it) != 0 }.toSet()
                    val answer = cache.targets(start, x)
                    assertEquals(expected, answer.toSet(), "edges=$edges mask=$mask start=$start")
                    assertEquals(answer.size, answer.toSet().size)
                    val before = evaluations
                    assertSame(answer, cache.targets(start, x))
                    assertEquals(before, evaluations, "An empty frontier is also cached")
                }
                assertEquals(3L, cache.searches)
                assertEquals(3L, cache.hits)
            }
        }
    }

    @Test fun `base and queried start own independent complete rows`() {
        val cache = CfgDeliveryCache(graph(listOf(listOf(1, 2), emptyList(), listOf(3), emptyList())), Cancellation()) { n, base ->
            if (base == x) n == 1 || n == 3 else n == 2
        }
        assertEquals(setOf(1, 3), cache.targets(0, x).toSet())
        assertEquals(setOf(2), cache.targets(0, y).toSet())
        assertEquals(setOf(3), cache.targets(2, x).toSet(), "A branch cannot borrow its parent's wider frontier")
        assertTrue(cache.targets(1, y).isEmpty())
    }

    @Test fun `cancellation cannot publish partial results and a later search completes`() {
        val cancellation = Cancellation()
        var cancel = true
        val cache = CfgDeliveryCache(graph(listOf(listOf(1, 2), emptyList(), emptyList())), cancellation) { n, _ ->
            if (n == 1 && cancel) cancellation.cancel()
            n != 0
        }
        assertFailsWith<Cancellation.Cancelled> { cache.targets(0, x) }
        assertEquals(0L, cache.searches)
        cancellation.activate(); cancel = false
        assertEquals(setOf(1, 2), cache.targets(0, x).toSet())
        assertEquals(1L, cache.searches)
        assertEquals(0L, cache.hits)
    }
}
