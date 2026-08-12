package org.opentaint.dataflow.ap.ifds.trace

import kotlin.test.Test
import kotlin.test.assertEquals

class GraphReachabilityUtilTest {
    private data class Edge(val target: String, val enabled: Boolean)

    @Test
    fun `reverse traversal finds every entry that can reach a target`() {
        val graph = mapOf(
            "root-a" to setOf(Edge("middle", enabled = true)),
            "root-b" to setOf(Edge("dead", enabled = true)),
            "middle" to setOf(Edge("target", enabled = true)),
            "dead" to setOf(Edge("target", enabled = false)),
        )

        val reachable = entriesThatCanReach(graph, setOf("target")) { edge ->
            edge.target.takeIf { edge.enabled }
        }

        assertEquals(setOf("root-a", "middle", "target"), reachable)
    }

    @Test
    fun `reverse traversal supports multiple targets and cycles`() {
        val graph = mapOf(
            1 to setOf(2),
            2 to setOf(1, 3),
            4 to setOf(5),
            6 to setOf(7),
        )

        assertEquals(
            setOf(1, 2, 3, 4, 5),
            entriesThatCanReach(graph, setOf(3, 5)) { it },
        )
    }
}
