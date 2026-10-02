package org.opentaint.dataflow.ap.ifds.markset

/**
 * The condensation of the part of a graph reachable from a set of start nodes.
 *
 * @property compOf the component of every node; `-1` for an unreachable node.
 * @property comps the members of every component, in reverse topological order:
 *   a component's successors all have smaller indices (callees before callers).
 * @property compSucc the distinct successor components of every component, excluding itself.
 */
class Condensation(val compOf: IntArray, val comps: List<IntArray>, val compSucc: Array<IntArray>)

object Scc {
    private const val UNVISITED = -1

    /**
     * Components in reverse topological order: callees before callers.
     * Iterative Tarjan, so deep call chains cannot overflow the stack.
     */
    fun condense(n: Int, succ: Array<IntArray>, reachableFrom: IntArray): Condensation {
        val index = IntArray(n) { UNVISITED }
        val low = IntArray(n)
        val onStack = BooleanArray(n)
        val compOf = IntArray(n) { -1 }
        val comps = mutableListOf<IntArray>()

        val stack = IntArray(n)
        var stackSize = 0
        // DFS frames: the node and the position of the next edge to explore.
        val frameNode = IntArray(n)
        val frameEdge = IntArray(n)
        var nextIndex = 0

        for (start in reachableFrom) {
            if (index[start] != UNVISITED) continue

            var depth = 0
            frameNode[0] = start
            frameEdge[0] = 0
            index[start] = nextIndex
            low[start] = nextIndex
            nextIndex++
            stack[stackSize++] = start
            onStack[start] = true

            while (depth >= 0) {
                val v = frameNode[depth]
                val edges = succ[v]
                val e = frameEdge[depth]
                if (e < edges.size) {
                    frameEdge[depth] = e + 1
                    val w = edges[e]
                    if (index[w] == UNVISITED) {
                        index[w] = nextIndex
                        low[w] = nextIndex
                        nextIndex++
                        stack[stackSize++] = w
                        onStack[w] = true
                        depth++
                        frameNode[depth] = w
                        frameEdge[depth] = 0
                    } else if (onStack[w]) {
                        low[v] = minOf(low[v], index[w])
                    }
                    continue
                }

                if (low[v] == index[v]) {
                    val comp = comps.size
                    var size = 0
                    while (true) {
                        val w = stack[stackSize - 1 - size]
                        size++
                        if (w == v) break
                    }
                    val members = IntArray(size)
                    for (i in 0 until size) {
                        val w = stack[--stackSize]
                        onStack[w] = false
                        compOf[w] = comp
                        members[i] = w
                    }
                    comps += members
                }

                depth--
                if (depth >= 0) {
                    val parent = frameNode[depth]
                    low[parent] = minOf(low[parent], low[v])
                }
            }
        }

        val compSucc = Array(comps.size) { c ->
            val out = LinkedHashSet<Int>()
            for (v in comps[c]) {
                for (w in succ[v]) {
                    val cw = compOf[w]
                    if (cw != c) out += cw
                }
            }
            out.toIntArray()
        }
        return Condensation(compOf, comps, compSucc)
    }
}
