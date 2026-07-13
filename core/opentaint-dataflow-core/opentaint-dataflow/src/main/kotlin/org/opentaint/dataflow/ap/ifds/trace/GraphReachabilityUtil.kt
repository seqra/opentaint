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
