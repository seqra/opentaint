package org.opentaint.common.sast.sarif

import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.longs.Long2IntOpenHashMap
import org.opentaint.dataflow.util.forEachInt
import java.util.PriorityQueue

internal const val BASE_COST = 1
internal const val COVERAGE_PENALTY = 10_000
internal const val EDGE_PENALTY = 1

internal class EdgePenalties {
    private val penalties = Long2IntOpenHashMap().apply { defaultReturnValue(0) }

    fun get(from: Int, to: Int): Int = penalties.get(packEdge(from, to))

    fun bump(from: Int, to: Int) {
        penalties.addTo(packEdge(from, to), EDGE_PENALTY)
    }

    private fun packEdge(from: Int, to: Int): Long =
        (from.toLong() shl 32) or (to.toLong() and 0xFFFF_FFFFL)
}

internal fun hopDistances(
    methodCount: Int,
    goals: IntOpenHashSet,
    forEachPredecessor: (node: Int, action: (Int) -> Unit) -> Unit,
): IntArray {
    val dist = IntArray(methodCount) { Int.MAX_VALUE }
    val queue = IntArrayList()

    val goalIter = goals.intIterator()
    while (goalIter.hasNext()) {
        val g = goalIter.nextInt()
        if (g in 0 until methodCount && dist[g] == Int.MAX_VALUE) {
            dist[g] = 0
            queue.add(g)
        }
    }

    var head = 0
    while (head < queue.size) {
        val node = queue.getInt(head++)
        val nextDist = dist[node] + 1
        forEachPredecessor(node) { pred ->
            if (pred in 0 until methodCount && dist[pred] == Int.MAX_VALUE) {
                dist[pred] = nextDist
                queue.add(pred)
            }
        }
    }

    return dist
}

private const val PHASE_SINK2ROOT = 0
private const val PHASE_ROOT2SOURCE = 1

internal class MethodTraceAStar(
    private val methodCount: Int,
    private val sink2RootEdges: (Int) -> IntOpenHashSet?,
    private val root2SourceEdges: (Int) -> IntOpenHashSet?,
    private val isRoot: (Int) -> Boolean,
    private val nodePenalty: IntArray,
    private val edgePenalties: EdgePenalties,
) {
    private fun nodeCost(method: Int): Int = BASE_COST + nodePenalty[method]

    private fun state(method: Int, phase: Int): Int = method * 2 + phase
    private fun stateMethod(state: Int): Int = state ushr 1
    private fun statePhase(state: Int): Int = state and 1

    data class SearchState(
        val score: Int,
        val state: Int,
        val g: Int,
    ) : Comparable<SearchState> {
        override fun compareTo(other: SearchState): Int =
            score.compareTo(other.score)
    }

    fun search(
        starts: IntOpenHashSet,
        isGoalSource: (Int) -> Boolean,
        heuristic: IntArray,
    ): MethodTrace? {
        val gScore = Int2IntOpenHashMap().apply { defaultReturnValue(Int.MAX_VALUE) }
        val cameFrom = Int2IntOpenHashMap().apply { defaultReturnValue(-1) }
        val open = PriorityQueue<SearchState>()

        fun h(method: Int): Int {
            val d = heuristic[method]
            return if (d == Int.MAX_VALUE) Int.MAX_VALUE else d * BASE_COST
        }

        fun push(state: Int, g: Int) {
            val hv = h(stateMethod(state))
            if (hv == Int.MAX_VALUE) return
            open.add(SearchState(g + hv, state, g))
        }

        fun relax(fromState: Int, toState: Int, stepCost: Int, gFrom: Int) {
            if (h(stateMethod(toState)) == Int.MAX_VALUE) return
            val newG = gFrom + stepCost
            if (newG < gScore.get(toState)) {
                gScore.put(toState, newG)
                cameFrom.put(toState, fromState)
                push(toState, newG)
            }
        }

        val startIter = starts.intIterator()
        while (startIter.hasNext()) {
            val s = startIter.nextInt()
            if (s !in 0 until methodCount || heuristic[s] == Int.MAX_VALUE) continue
            val st = state(s, PHASE_SINK2ROOT)
            val g = nodeCost(s)
            if (g < gScore.get(st)) {
                gScore.put(st, g)
                push(st, g)
            }
        }

        while (open.isNotEmpty()) {
            val top = open.poll()
            val state = top.state
            val g = top.g
            if (g > gScore.get(state)) continue

            val method = stateMethod(state)
            val phase = statePhase(state)

            if (phase == PHASE_ROOT2SOURCE && isGoalSource(method)) {
                return reconstruct(state, cameFrom)
            }

            if (phase == PHASE_SINK2ROOT) {
                if (isRoot(method)) {
                    // zero-cost phase switch on the same method (no node re-charge)
                    relax(state, state(method, PHASE_ROOT2SOURCE), stepCost = 0, gFrom = g)
                }
                sink2RootEdges(method)?.forEachInt { next ->
                    val step = edgePenalties.get(method, next) + nodeCost(next)
                    relax(state, state(next, PHASE_SINK2ROOT), step, g)
                }
            } else {
                root2SourceEdges(method)?.forEachInt { next ->
                    val step = edgePenalties.get(method, next) + nodeCost(next)
                    relax(state, state(next, PHASE_ROOT2SOURCE), step, g)
                }
            }
        }

        return null
    }

    private fun reconstruct(goalState: Int, cameFrom: Int2IntOpenHashMap): MethodTrace {
        val states = IntArrayList()
        var s = goalState
        while (s != -1) {
            states.add(s)
            s = cameFrom.get(s)
        }
        // states is goal->start. Walk start->goal, splitting by phase.
        val sink2Root = IntArrayList()
        val root2Source = IntArrayList()
        for (i in states.size - 1 downTo 0) {
            val st = states.getInt(i)
            val m = stateMethod(st)
            if (statePhase(st) == PHASE_SINK2ROOT) sink2Root.add(m) else root2Source.add(m)
        }
        return MethodTrace(sink2Root.toIntArray(), root2Source.toIntArray())
    }
}

internal inline fun MethodTrace.forEachNode(action: (Int) -> Unit) {
    for (m in sink2Root) action(m)
    for (m in root2Source) action(m)
}

private inline fun forEachEdge(path: IntArray, action: (from: Int, to: Int) -> Unit) {
    for (i in 0 until path.size - 1) action(path[i], path[i + 1])
}

private fun sameTrace(a: MethodTrace, b: MethodTrace): Boolean =
    a.sink2Root.contentEquals(b.sink2Root) && a.root2Source.contentEquals(b.root2Source)

private fun singleton(value: Int): IntOpenHashSet = IntOpenHashSet().apply { add(value) }

internal fun <T : Any> selectMethodTraces(
    methodCount: Int,
    sinkMethods: IntOpenHashSet,
    rootMethods: IntOpenHashSet,
    sourceMethods: IntOpenHashSet,
    sink2RootEdges: (Int) -> IntOpenHashSet?,
    root2SourceEdges: (Int) -> IntOpenHashSet?,
    forEachPredecessor: (node: Int, action: (Int) -> Unit) -> Unit,
    cap: Int,
    collect: (MethodTrace) -> T?,
): List<T> {
    if (cap <= 0 || methodCount == 0) return emptyList()

    val result = mutableListOf<T>()
    val coveredNodes = IntOpenHashSet()
    val nodePenalty = IntArray(methodCount)
    val edgePenalties = EdgePenalties()
    val astar = MethodTraceAStar(
        methodCount, sink2RootEdges, root2SourceEdges,
        { rootMethods.contains(it) }, nodePenalty, edgePenalties,
    )

    var noProgress = 0

    fun bumpEdges(trace: MethodTrace) {
        forEachEdge(trace.sink2Root) { a, b -> edgePenalties.bump(a, b) }
        forEachEdge(trace.root2Source) { a, b -> edgePenalties.bump(a, b) }
    }

    fun markCovered(trace: MethodTrace): Boolean {
        var newCovered = false
        trace.forEachNode { n ->
            if (coveredNodes.add(n)) {
                nodePenalty[n] = COVERAGE_PENALTY
                newCovered = true
            }
        }
        return newCovered
    }

    fun addsNewNode(trace: MethodTrace): Boolean {
        trace.forEachNode {
            if (!coveredNodes.contains(it)) return true
        }
        return false
    }

    fun searchTraces(sourceMethods: IntOpenHashSet, sinkMethods: IntOpenHashSet, searchMultipleTraces: Boolean) {
        val heuristic = hopDistances(methodCount, sourceMethods, forEachPredecessor)

        var prev: MethodTrace? = null
        while (result.size < cap && coveredNodes.size < methodCount) {
            val trace = astar.search(sinkMethods, { sourceMethods.contains(it) }, heuristic) ?: break
            bumpEdges(trace)
            if (addsNewNode(trace)) {
                val res = collect(trace)
                if (res != null) {
                    result.add(res)
                    if (markCovered(trace)) noProgress = 0
                    if (searchMultipleTraces) {
                        prev = null
                        continue
                    } else {
                        break
                    }
                }
            }
            noProgress++
            if (noProgress >= methodCount) break
            if (prev != null && sameTrace(prev, trace)) break
            prev = trace
        }
    }

    // Pass 1: forcibly cover (sink, source) pairs — one accepted trace per pair.
    val sinkIter = sinkMethods.intIterator()
    while (sinkIter.hasNext() && result.size < cap) {
        val sink = sinkIter.nextInt()
        val srcIter = sourceMethods.intIterator()
        while (srcIter.hasNext() && result.size < cap) {
            val source = srcIter.nextInt()
            searchTraces(singleton(source), singleton(sink), searchMultipleTraces = false)
        }
    }

    // Pass 2: cover remaining uncovered nodes — unbounded over sinks/sources.
    if (result.size < cap && coveredNodes.size < methodCount) {
        searchTraces(sourceMethods, sinkMethods, searchMultipleTraces = true)
    }

    return result
}
