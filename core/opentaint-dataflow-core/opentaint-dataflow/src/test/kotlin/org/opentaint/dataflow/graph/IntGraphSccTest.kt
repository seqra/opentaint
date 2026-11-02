package org.opentaint.dataflow.graph

import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals

class IntGraphSccTest {
    @Test fun `iterative traversal preserves the Tarjan component and member order`() {
        val graph = IntGraph()
        for ((a, b) in listOf(0 to 1, 1 to 2, 2 to 0, 1 to 3, 3 to 4,
                4 to 3, 4 to 5, 6 to 6)) graph.addEdge(a, b)
        assertEquals(listOf(setOf(5), setOf(3, 4), setOf(0, 1, 2), setOf(6)),
            graph.allSccs().map { set -> set.stream().boxed().toList().toSet() })
        assertEquals(listOf(setOf(3, 4), setOf(0, 1, 2), setOf(6)),
            graph.nonTrivialSccs().map { set -> set.stream().boxed().toList().toSet() })
    }

    @Test fun `deep acyclic traversal and a deep cycle use no recursive DFS stack`() {
        val size = 12000
        val graph = IntGraph()
        for (index in 0 until size - 1) graph.addEdge(index, index + 1)
        val components = graph.allSccs()
        assertEquals(size, components.size)
        assertEquals(size - 1, components.first().nextSetBit(0))
        assertEquals(0, components.last().nextSetBit(0))
        graph.addEdge(size - 1, 0)
        assertEquals(listOf(BitSet(size).apply { set(0, size) }), graph.allSccs())
    }
}
