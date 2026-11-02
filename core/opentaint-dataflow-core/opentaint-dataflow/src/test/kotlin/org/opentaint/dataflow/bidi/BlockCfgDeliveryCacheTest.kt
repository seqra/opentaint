package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.engine.BlockCfgDeliveryCache
import org.opentaint.dataflow.bidi.engine.BlockDeliveryTarget
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.graph.MethodBlockLayoutBuilder
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

class BlockCfgDeliveryCacheTest {
    private val x = AccessPathBase.Argument(0)
    private val y = AccessPathBase.Argument(1)
    private fun graph(size: Int, vararg edges: Pair<Int, Int>) = CompactGraph.build(size) { from ->
        BitSet(size).apply { edges.forEach { if (it.first == from) set(it.second) } }
    }

    @Test fun `neutral traversal stops at both repeat and leave boundaries before another block`() {
        val graph = graph(5, 0 to 1, 1 to 2, 2 to 1, 1 to 3, 3 to 4)
        val layout = MethodBlockLayoutBuilder.build(graph, listOf(0))
        val loop = layout.ownerOf(1)
        var evaluations = 0
        val cache = BlockCfgDeliveryCache(layout, graph, loop, false, Cancellation()) { _, _ ->
            evaluations++; false
        }
        val first = cache.targets(1, x)
        assertEquals(setOf(1 to 3, 2 to 1), first.map {
            val route = assertIs<BlockDeliveryTarget.Boundary>(it).route
            route.from to route.to
        }.toSet())
        assertEquals(loop, first.filterIsInstance<BlockDeliveryTarget.Boundary>()
            .single { it.route.from == 2 }.route.feedbackLoop)
        val before = evaluations
        assertEquals(first, cache.targets(1, x))
        assertEquals(before, evaluations)
        assertEquals(1L, cache.hits)
        assertEquals(1L, cache.searches)
        assertFailsWith<IllegalArgumentException> { cache.targets(3, x) }
    }

    @Test fun `first relevant instruction can be delivered but never bypasses its loop boundary`() {
        val graph = graph(5, 0 to 1, 1 to 2, 2 to 1, 1 to 3, 3 to 4)
        val layout = MethodBlockLayoutBuilder.build(graph, listOf(0))
        val cache = BlockCfgDeliveryCache(layout, graph, layout.ownerOf(1), false, Cancellation()) { n, base ->
            base == x && n == 2
        }
        assertEquals(setOf(2), cache.targets(1, x).filterIsInstance<BlockDeliveryTarget.Statement>().map { it.index }.toSet())
        assertEquals(setOf(1 to 3), cache.targets(1, x).filterIsInstance<BlockDeliveryTarget.Boundary>()
            .map { it.route.from to it.route.to }.toSet())
        val after = cache.after(2, x)
        val repeat = assertIs<BlockDeliveryTarget.Boundary>(after.single())
        assertEquals(2 to 1, repeat.route.from to repeat.route.to)
        assertEquals(2, cache.targets(1, y).size)
    }

    @Test fun `ZERO preserves every original operation and still routes a self loop through a boundary`() {
        val graph = graph(3, 0 to 1, 1 to 1, 1 to 2)
        val layout = MethodBlockLayoutBuilder.build(graph, listOf(0))
        val cache = BlockCfgDeliveryCache(layout, graph, layout.ownerOf(1), false, Cancellation()) { _, _ ->
            error("ZERO must not consult base relevance")
        }
        assertEquals(listOf(BlockDeliveryTarget.Statement(1)), cache.targets(1, AccessPathBase.Zero))
        val after = cache.after(1, AccessPathBase.Zero).map { assertIs<BlockDeliveryTarget.Boundary>(it).route }
        assertEquals(setOf(1 to 1, 1 to 2), after.map { it.from to it.to }.toSet())
        assertTrue(after.single { it.to == 1 }.feedbackLoop != null)
        assertEquals(0L, cache.searches)
    }

    @Test fun `backward view stops on reversed feedback and preserves exceptional discovery`() {
        val forward = graph(5, 0 to 1, 1 to 2, 2 to 1)
        val backward = CompactGraph.build(5) { from -> BitSet(5).apply {
            forward.forEachPredecessor(from) { set(it) }
            if (from == 4) set(1)
        } }
        val layout = MethodBlockLayoutBuilder.build(forward, listOf(0))
        val loop = BlockCfgDeliveryCache(layout, backward, layout.ownerOf(1), true, Cancellation()) { _, _ -> false }
        val repeated = loop.targets(1, x).filterIsInstance<BlockDeliveryTarget.Boundary>().map { it.route }
        assertTrue(repeated.any { it.from == 1 && it.to == 2 && it.feedbackLoop != null })
        val exceptional = BlockCfgDeliveryCache(layout, backward, layout.ownerOf(4), true, Cancellation()) { _, _ -> false }
        val discovery = assertIs<BlockDeliveryTarget.Boundary>(exceptional.after(4, AccessPathBase.Zero).single())
        assertTrue(discovery.route.discovery)
        assertEquals(4 to 1, discovery.route.from to discovery.route.to)
        assertFalse(discovery.route.feedbackLoop != null)
    }

    @Test fun `completed empty result is cached but a cancelled search publishes no row`() {
        val graph = graph(3, 0 to 1, 0 to 2)
        val layout = MethodBlockLayoutBuilder.build(graph, listOf(0))
        val cancellation = Cancellation()
        var cancel = true
        var checks = 0
        val cache = BlockCfgDeliveryCache(layout, graph, layout.root, false, cancellation) { n, _ ->
            checks++
            if (cancel && n == 1) cancellation.cancel()
            false
        }
        assertFailsWith<Cancellation.Cancelled> { cache.targets(0, x) }
        assertEquals(0L, cache.searches)
        cancellation.activate(); cancel = false
        assertTrue(cache.targets(0, x).isEmpty())
        val before = checks
        assertTrue(cache.targets(0, x).isEmpty())
        assertEquals(before, checks)
        assertEquals(1L, cache.hits)
        assertEquals(1L, cache.searches)
    }

    @Test fun `an original root boundary stops delivery even with the same lowest owner`() {
        val graph = graph(3, 0 to 1, 1 to 2)
        val layout = MethodBlockLayoutBuilder.build(graph, listOf(0))
        val cache = BlockCfgDeliveryCache(layout, graph, layout.root, false, Cancellation(),
            boundaryTarget = { it == 2 }) { _, _ -> false }
        val target = assertIs<BlockDeliveryTarget.Boundary>(cache.targets(0, x).single())
        assertEquals(1 to 2, target.route.from to target.route.to)
        assertFalse(target.route.crossesBoundary, "The original method boundary is an explicit stop")
        assertEquals(listOf(target), cache.after(1, AccessPathBase.Zero))
        assertEquals(listOf(target), cache.targets(0, x))
        assertEquals(1L, cache.hits)
    }
}
