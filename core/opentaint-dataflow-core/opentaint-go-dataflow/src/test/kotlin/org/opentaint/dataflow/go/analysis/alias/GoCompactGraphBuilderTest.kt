package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.graph.CompactGraph
import java.util.BitSet
import kotlin.test.Test
import kotlin.test.assertEquals

class GoCompactGraphBuilderTest {
    @Test
    fun `linear graph has single successors`() {
        val g = CompactGraph.build(3) { i -> BitSet().apply { if (i < 2) set(i + 1) } }
        val succ = mutableListOf<Int>()
        g.forEachSuccessor(0) { succ.add(it) }
        assertEquals(listOf(1), succ)
        val exits = mutableListOf<Int>()
        g.forEachSuccessor(2) { exits.add(it) }
        assertEquals(emptyList(), exits)
    }
}
