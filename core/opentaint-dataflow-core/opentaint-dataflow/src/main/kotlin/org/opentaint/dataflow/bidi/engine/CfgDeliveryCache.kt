package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet

/** One actor, graph direction and rule view. Rows contain no facts or forms. */
internal class CfgDeliveryCache(
    private val graph: CompactGraph,
    private val cancellation: Cancellation,
    private val relevant: (Int, AccessPathBase) -> Boolean,
) {
    private val rows = arrayOfNulls<MutableMap<AccessPathBase, IntArray>>(graph.size)
    var hits = 0L; private set
    var searches = 0L; private set
    var visitedNodes = 0L; private set
    var destinations = 0L; private set
    var maxWidth = 0; private set

    /** Borrowed immutable first-relevant frontier. Empty is a completed hit. */
    fun targets(start: Int, base: AccessPathBase): IntArray {
        cancellation.checkpoint()
        rows[start]?.get(base)?.let { hits++; return it }
        val visited = BitSet(graph.size)
        val todo = IntArray(graph.size)
        var read = 0
        var write = 1
        todo[0] = start
        visited.set(start)
        val found = ArrayList<Int>()
        while (read < write) {
            cancellation.checkpoint()
            val node = todo[read++]
            if (relevant(node, base)) found += node
            else graph.forEachSuccessor(node) { next ->
                if (!visited[next]) { visited.set(next); todo[write++] = next }
            }
        }
        // A cancelled traversal never publishes a partial or empty placeholder.
        cancellation.checkpoint()
        val result = found.toIntArray()
        val row = rows[start] ?: HashMap<AccessPathBase, IntArray>().also { rows[start] = it }
        row[base] = result
        searches++
        visitedNodes += read
        destinations += result.size
        maxWidth = maxOf(maxWidth, result.size)
        return result
    }
}
