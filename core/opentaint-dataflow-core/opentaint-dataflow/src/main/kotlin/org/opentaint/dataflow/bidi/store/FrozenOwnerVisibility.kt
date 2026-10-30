package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.util.Cancellation

/** Exact caller-to-owner reachability. Rows are immutable after the run-1 handoff. */
internal class FrozenOwnerVisibility private constructor(
    private val componentOfMethod: IntArray,
    private val wordsByComponent: Array<LongArray>,
    val familyCount: Int,
    val statistics: BuildStatistics,
) {
    data class BuildStatistics(
        val components: Int,
        val dagEdges: Long,
        val seedMemberships: Long,
        val allocatedWords: Long,
        val buildNanos: Long,
    )

    fun contains(methodId: Int?, familyId: Int): Boolean {
        if (methodId == null) return false
        val row = wordsByComponent[componentOfMethod[methodId]]
        return row[familyId ushr 6] and (1L shl (familyId and 63)) != 0L
    }

    /** Read-only certificate for independent finite-graph tests. */
    internal fun componentId(methodId: Int): Int = componentOfMethod[methodId]

    class Builder(
        graph: DetachedStaticCallGraph,
        private val familyCount: Int,
        private val cancellation: Cancellation,
    ) {
        private val started = System.nanoTime()
        private val component: IntArray
        private val dag: Array<IntArray>
        private val callerFirst: IntArray
        private val words: Array<LongArray>
        private var seedMemberships = 0L
        private var finished = false

        init {
            cancellation.checkpoint()
            require(familyCount >= 0)
            if (familyCount == 0) {
                // No query can use this index. Do not traverse an otherwise large graph.
                component = IntArray(0)
                dag = emptyArray()
                callerFirst = IntArray(0)
                words = emptyArray()
            } else {
                val components = components(graph, cancellation)
                component = components.first
                dag = quotient(graph, component, components.second, cancellation)
                callerFirst = topologicalOrder(dag, cancellation)
                val wordCount = familyCount / 64 + if (familyCount % 64 == 0) 0 else 1
                words = Array(dag.size) { cancellation.checkpoint(); LongArray(wordCount) }
            }
        }

        fun seed(familyId: Int, ownerId: Int) {
            cancellation.checkpoint()
            check(!finished)
            val row = words[component[ownerId]]
            row[familyId ushr 6] = row[familyId ushr 6] or (1L shl (familyId and 63))
            seedMemberships++
        }

        fun finish(): FrozenOwnerVisibility {
            cancellation.checkpoint()
            check(!finished)
            // Every child row is complete before its parent consumes it.
            for (position in callerFirst.lastIndex downTo 0) {
                cancellation.checkpoint()
                val parent = callerFirst[position]
                val into = words[parent]
                for (child in dag[parent]) {
                    cancellation.checkpoint()
                    val from = words[child]
                    for (word in into.indices) {
                        cancellation.checkpoint()
                        into[word] = into[word] or from[word]
                    }
                }
            }
            finished = true
            val stats = BuildStatistics(dag.size, dag.sumOf { it.size.toLong() }, seedMemberships,
                words.sumOf { it.size.toLong() }, System.nanoTime() - started)
            return FrozenOwnerVisibility(component, words, familyCount, stats)
        }

        companion object {
            /** Iterative Kosaraju. Mark on push, so each stack has at most N entries. */
            private fun components(graph: DetachedStaticCallGraph, cancellation: Cancellation): Pair<IntArray, Int> {
                val size = graph.methodCount
                val seen = BooleanArray(size)
                val cursor = IntArray(size)
                val stack = IntArray(size)
                val finish = IntArray(size)
                var finished = 0
                var pending = 0
                for (root in 0 until size) {
                    cancellation.checkpoint()
                    if (seen[root]) continue
                    stack[pending++] = root
                    seen[root] = true
                    while (pending > 0) {
                        cancellation.checkpoint()
                        val vertex = stack[pending - 1]
                        if (cursor[vertex] < graph.outDegree(vertex)) {
                            val child = graph.calleeAt(vertex, cursor[vertex]++)
                            if (!seen[child]) {
                                seen[child] = true
                                stack[pending++] = child
                            }
                        } else {
                            pending--
                            finish[finished++] = vertex
                        }
                    }
                }

                val reverseSize = IntArray(size)
                for (vertex in 0 until size) {
                    cancellation.checkpoint()
                    for (i in 0 until graph.outDegree(vertex)) {
                        cancellation.checkpoint()
                        reverseSize[graph.calleeAt(vertex, i)]++
                    }
                }
                val reverse = Array(size) { cancellation.checkpoint(); IntArray(reverseSize[it]) }
                reverseSize.fill(0)
                for (vertex in 0 until size) {
                    cancellation.checkpoint()
                    for (i in 0 until graph.outDegree(vertex)) {
                        cancellation.checkpoint()
                        val child = graph.calleeAt(vertex, i)
                        reverse[child][reverseSize[child]++] = vertex
                    }
                }

                val component = IntArray(size) { -1 }
                var componentCount = 0
                for (position in finished - 1 downTo 0) {
                    cancellation.checkpoint()
                    val root = finish[position]
                    if (component[root] >= 0) continue
                    val id = componentCount++
                    component[root] = id
                    stack[pending++] = root
                    while (pending > 0) {
                        cancellation.checkpoint()
                        val vertex = stack[--pending]
                        for (parent in reverse[vertex]) {
                            cancellation.checkpoint()
                            if (component[parent] < 0) {
                                component[parent] = id
                                stack[pending++] = parent
                            }
                        }
                    }
                }
                return component to componentCount
            }

            private fun quotient(
                graph: DetachedStaticCallGraph, component: IntArray, count: Int, cancellation: Cancellation,
            ): Array<IntArray> {
                val outgoing = Array(count) { cancellation.checkpoint(); IntArrayList() }
                for (vertex in 0 until graph.methodCount) {
                    cancellation.checkpoint()
                    val parent = component[vertex]
                    for (i in 0 until graph.outDegree(vertex)) {
                        cancellation.checkpoint()
                        val child = component[graph.calleeAt(vertex, i)]
                        if (child != parent) outgoing[parent].add(child)
                    }
                }
                return Array(count) { parent ->
                    cancellation.checkpoint()
                    val children = outgoing[parent].toIntArray()
                    children.sort()
                    var size = 0
                    for (child in children) {
                        cancellation.checkpoint()
                        if (size == 0 || children[size - 1] != child) children[size++] = child
                    }
                    if (size == children.size) children else children.copyOf(size)
                }
            }

            /** Explicit Kahn order. Component numbering is not a rank contract. */
            private fun topologicalOrder(dag: Array<IntArray>, cancellation: Cancellation): IntArray {
                val incoming = IntArray(dag.size)
                for (children in dag) {
                    cancellation.checkpoint()
                    for (child in children) { cancellation.checkpoint(); incoming[child]++ }
                }
                val order = IntArray(dag.size)
                var read = 0
                var write = 0
                for (vertex in incoming.indices) {
                    cancellation.checkpoint()
                    if (incoming[vertex] == 0) order[write++] = vertex
                }
                while (read < write) {
                    cancellation.checkpoint()
                    for (child in dag[order[read++]]) {
                        cancellation.checkpoint()
                        if (--incoming[child] == 0) order[write++] = child
                    }
                }
                check(write == dag.size) { "SCC quotient has a cycle" }
                return order
            }
        }
    }
}
