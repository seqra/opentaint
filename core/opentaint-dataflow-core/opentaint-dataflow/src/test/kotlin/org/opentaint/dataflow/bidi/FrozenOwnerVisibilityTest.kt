package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.store.DetachedStaticCallGraph
import org.opentaint.dataflow.bidi.store.FrozenOwnerVisibility
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.*

class FrozenOwnerVisibilityTest {
    private class Method(override val name: String) : CommonMethod {
        override val parameters: List<CommonMethodParameter> = emptyList()
        override val returnType = object : CommonTypeName { override val typeName = "Object" }
        override fun flowGraph(): ControlFlowGraph<CommonInst> = error("unused")
    }

    private fun graph(edges: Array<IntArray>, cancellation: Cancellation): Pair<DetachedStaticCallGraph, IntArray> {
        val methods = Array(edges.size) { Method("m$it") }
        val source = linkedMapOf<CommonMethod, Set<CommonMethod>>()
        // Include isolated methods. The detached graph may assign a child before its source.
        for (i in methods.indices) source[methods[i]] = edges[i].mapTo(linkedSetOf()) { methods[it] }
        val graph = DetachedStaticCallGraph.copyOf(source, cancellation)
        return graph to IntArray(methods.size) { checkNotNull(graph.id(methods[it])) }
    }

    private fun reachable(edges: Array<IntArray>, from: Int): BooleanArray {
        val seen = BooleanArray(edges.size)
        val pending = ArrayDeque<Int>()
        seen[from] = true
        pending.add(from)
        while (pending.isNotEmpty()) for (child in edges[pending.removeFirst()]) if (!seen[child]) {
            seen[child] = true
            pending.add(child)
        }
        return seen
    }

    @Test fun `all graphs up to three vertices preserve owner families and component certificates`() {
        val cancellation = Cancellation()
        for (n in 1..3) for (mask in 0 until (1 shl (n * n))) {
            val edges = Array(n) { from -> (0 until n).filter { to -> mask and (1 shl (from * n + to)) != 0 }.toIntArray() }
            val (graph, ids) = graph(edges, cancellation)
            val familyCount = 1 shl n
            val builder = FrozenOwnerVisibility.Builder(graph, familyCount, cancellation)
            for (family in 0 until familyCount) for (owner in 0 until n)
                if (family and (1 shl owner) != 0) builder.seed(family, ids[owner])
            val index = builder.finish()
            val paths = Array(n) { reachable(edges, it) }
            for (from in 0 until n) {
                for (family in 0 until familyCount) {
                    val expected = (0 until n).any { family and (1 shl it) != 0 && paths[from][it] }
                    assertEquals(expected, index.contains(ids[from], family), "n=$n graph=$mask from=$from owners=$family")
                }
                for (to in 0 until n) assertEquals(paths[from][to] && paths[to][from],
                    index.componentId(ids[from]) == index.componentId(ids[to]), "SCC certificate: n=$n graph=$mask $from/$to")
            }
            assertFalse(index.contains(null, familyCount - 1))
        }
    }

    @Test fun `diamond disconnected components and packed word boundaries preserve each original family`() {
        val cancellation = Cancellation()
        val edges = arrayOf(intArrayOf(1, 2), intArrayOf(3), intArrayOf(3), intArrayOf(), intArrayOf())
        val (graph, ids) = graph(edges, cancellation)
        val builder = FrozenOwnerVisibility.Builder(graph, 130, cancellation)
        for (family in 0 until 130) builder.seed(family, ids[if (family % 2 == 0) 3 else 4])
        val index = builder.finish()
        for (family in 0 until 130) {
            assertEquals(family % 2 == 0, index.contains(ids[0], family))
            assertEquals(family % 2 != 0, index.contains(ids[4], family))
        }
        assertEquals(5, index.statistics.components)
        assertEquals(4L, index.statistics.dagEdges)
        assertEquals(15L, index.statistics.allocatedWords)
        assertEquals(130L, index.statistics.seedMemberships)
    }

    @Test fun `long chain and one large recursive component do not use JVM recursion`() {
        val cancellation = Cancellation()
        val size = 20_000
        for (cycle in listOf(false, true)) {
            val edges = Array(size) { i -> if (i + 1 < size) intArrayOf(i + 1)
                else if (cycle) intArrayOf(0) else intArrayOf() }
            val (graph, ids) = graph(edges, cancellation)
            val builder = FrozenOwnerVisibility.Builder(graph, 2, cancellation)
            builder.seed(0, ids.last())
            builder.seed(1, ids.first())
            val index = builder.finish()
            assertTrue(index.contains(ids.first(), 0))
            assertTrue(index.contains(ids.last(), 0), "Length-zero owner path")
            assertEquals(cycle, index.contains(ids.last(), 1))
            assertEquals(if (cycle) 1 else size, index.statistics.components)
        }
    }

    @Test fun `empty graph outside-only families and zero-family builds require no graph work`() {
        val cancellation = Cancellation()
        val empty = FrozenOwnerVisibility.Builder(DetachedStaticCallGraph.EMPTY, 129, cancellation).finish()
        assertFalse(empty.contains(null, 128))
        assertEquals(0L, empty.statistics.allocatedWords)
        assertEquals(0, empty.statistics.components)
        val (graph, _) = graph(arrayOf(intArrayOf(1), intArrayOf()), cancellation)
        val noFamilies = FrozenOwnerVisibility.Builder(graph, 0, cancellation).finish()
        assertEquals(0L, noFamilies.statistics.allocatedWords)
        assertEquals(0, noFamilies.statistics.components, "No owner family needs a component build")
    }

    @Test fun `cancellation before construction or finish cannot publish an incomplete index`() {
        val cancellation = Cancellation()
        cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { FrozenOwnerVisibility.Builder(DetachedStaticCallGraph.EMPTY, 1, cancellation) }
        cancellation.activate()
        val builder = FrozenOwnerVisibility.Builder(DetachedStaticCallGraph.EMPTY, 1, cancellation)
        cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { builder.finish() }
    }
}
