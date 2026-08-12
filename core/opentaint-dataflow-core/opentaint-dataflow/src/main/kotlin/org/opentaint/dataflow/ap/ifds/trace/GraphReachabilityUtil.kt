package org.opentaint.dataflow.ap.ifds.trace

inline fun <T : Any, Edge> entriesReachableFrom(
    successors: Map<T, Set<Edge>>,
    start: T,
    target: Set<T>,
    edgeEntry: (Edge) -> T?
): Boolean {
    val visited = hashSetOf<T>()
    val unprocessed = mutableListOf(start)
    while (unprocessed.isNotEmpty()) {
        val entry = unprocessed.removeLast()
        if (!visited.add(entry)) continue

        if (entry in target) return true

        successors[entry]?.forEach { edge ->
            edgeEntry(edge)?.let { unprocessed.add(it) }
        }
    }
    return false
}

/**
 * Returns every entry that can reach at least one [target] through edges accepted by [edgeEntry].
 * The reverse graph is built once, so the cost is linear in the graph rather than one traversal
 * per possible start entry.
 */
inline fun <T : Any, Edge> entriesThatCanReach(
    successors: Map<T, Set<Edge>>,
    target: Set<T>,
    edgeEntry: (Edge) -> T?,
): Set<T> {
    val predecessors = hashMapOf<T, MutableList<T>>()
    for ((from, edges) in successors) {
        for (edge in edges) {
            val to = edgeEntry(edge) ?: continue
            predecessors.getOrPut(to, ::arrayListOf).add(from)
        }
    }

    val reachable = hashSetOf<T>()
    val unprocessed = target.toMutableList()
    while (unprocessed.isNotEmpty()) {
        val entry = unprocessed.removeLast()
        if (!reachable.add(entry)) continue
        predecessors[entry]?.let(unprocessed::addAll)
    }
    return reachable
}
