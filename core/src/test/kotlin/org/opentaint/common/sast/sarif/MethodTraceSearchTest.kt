package org.opentaint.common.sast.sarif

import io.mockk.mockk
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.junit.jupiter.api.Test
import org.opentaint.ir.api.common.CommonMethod
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class MethodTraceSearchTest {
    @Test
    fun edgePenaltiesStartAtZeroAndAccumulate() {
        val penalties = EdgePenalties()
        assertEquals(0, penalties.get(1, 2))

        penalties.bump(1, 2)
        penalties.bump(1, 2)
        assertEquals(2 * EDGE_PENALTY, penalties.get(1, 2))

        // direction matters: (2,1) is a different edge
        assertEquals(0, penalties.get(2, 1))
    }

    @Test
    fun hopDistancesAreEdgeCountsToNearestGoal() {
        // forward chain 0 -> 1 -> 2 -> 3 -> 4, goal = {4}
        val preds = predecessorsOf(0 to 1, 1 to 2, 2 to 3, 3 to 4)
        val dist = hopDistances(methodCount = 5, goals = intSet(4), forEachPredecessor = preds)

        assertEquals(0, dist[4])
        assertEquals(1, dist[3])
        assertEquals(2, dist[2])
        assertEquals(3, dist[1])
        assertEquals(4, dist[0])
    }

    @Test
    fun hopDistancesAreMaxValueForUnreachableNodes() {
        val preds = predecessorsOf(0 to 1) // 2 cannot reach goal 1
        val dist = hopDistances(methodCount = 3, goals = intSet(1), forEachPredecessor = preds)

        assertEquals(0, dist[1])
        assertEquals(1, dist[0])
        assertEquals(Int.MAX_VALUE, dist[2])
    }

    @Test
    fun aStarFindsTheOnlyTrace() {
        // sink 0 -> 1 -> root 2 -> 3 -> source 4
        val sink2Root = mapOf(0 to intSet(1), 1 to intSet(2))
        val root2Source = mapOf(2 to intSet(3), 3 to intSet(4))
        val preds = predecessorsOf(0 to 1, 1 to 2, 2 to 3, 3 to 4)

        val astar = MethodTraceAStar(
            methodCount = 5,
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            isRoot = { it == 2 },
            nodePenalty = IntArray(5),
            edgePenalties = EdgePenalties(),
        )
        val h = hopDistances(5, intSet(4), preds)

        val trace = astar.search(starts = intSet(0), isGoalSource = { it == 4 }, heuristic = h)!!

        assertEquals(listOf(0, 1, 2), trace.sink2Root.toList())
        assertEquals(listOf(2, 3, 4), trace.root2Source.toList())
    }

    @Test
    fun aStarAvoidsCoveredNodesViaNodePenalty() {
        // two equal-length sink->root branches through 1 or 5; node 1 is "covered".
        val sink2Root = mapOf(0 to intSet(1, 5), 1 to intSet(2), 5 to intSet(2))
        val root2Source = mapOf(2 to intSet(3))
        val preds = predecessorsOf(0 to 1, 0 to 5, 1 to 2, 5 to 2, 2 to 3)
        val nodePenalty = IntArray(6)
        nodePenalty[1] = COVERAGE_PENALTY

        val astar = MethodTraceAStar(
            methodCount = 6,
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            isRoot = { it == 2 },
            nodePenalty = nodePenalty,
            edgePenalties = EdgePenalties(),
        )
        val h = hopDistances(6, intSet(3), preds)

        val trace = astar.search(intSet(0), { it == 3 }, h)!!

        assertEquals(listOf(0, 5, 2), trace.sink2Root.toList())
        assertEquals(listOf(2, 3), trace.root2Source.toList())
    }

    @Test
    fun aStarReturnsNullWhenNoSourceReachable() {
        val sink2Root = mapOf(0 to intSet(1)) // 1 is a root but reaches no source
        val root2Source = emptyMap<Int, IntOpenHashSet>()
        val preds = predecessorsOf(0 to 1) // goal 9 unreachable

        val astar = MethodTraceAStar(
            methodCount = 10,
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            isRoot = { it == 1 },
            nodePenalty = IntArray(10),
            edgePenalties = EdgePenalties(),
        )
        val h = hopDistances(10, intSet(9), preds)

        assertEquals(null, astar.search(intSet(0), { it == 9 }, h))
    }

    @Test
    fun driverCoversEveryNodeAndKeepsUncoveredPenaltyZero() {
        // sink 0 -> root 1 -> source 2  (a single linear trace)
        val sink2Root = mapOf(0 to intSet(1))
        val root2Source = mapOf(1 to intSet(2))
        val preds: (Int, (Int) -> Unit) -> Unit = predecessorsOf(0 to 1, 1 to 2)
        val recorded = mutableListOf<Pair<List<Int>, List<Int>>>()

        val result = selectMethodTraces(
            methodCount = 3,
            sinkMethods = intSet(0),
            rootMethods = intSet(1),
            sourceMethods = intSet(2),
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            forEachPredecessor = preds,
            cap = Int.MAX_VALUE,
            collect = recordingCollect(recorded),
        )

        assertEquals(1, result.size)
        assertEquals(listOf(0, 1) to listOf(1, 2), recorded.single())
    }

    @Test
    fun driverTerminatesWhenEveryCandidateIsDiscarded() {
        // structurally connected, but collect always rejects -> must terminate (N-cap / single-path lookback).
        val sink2Root = mapOf(0 to intSet(1))
        val root2Source = mapOf(1 to intSet(2))
        val preds: (Int, (Int) -> Unit) -> Unit = predecessorsOf(0 to 1, 1 to 2)
        var checks = 0

        val result = selectMethodTraces(
            methodCount = 3,
            sinkMethods = intSet(0),
            rootMethods = intSet(1),
            sourceMethods = intSet(2),
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            forEachPredecessor = preds,
            cap = Int.MAX_VALUE,
            collect = { checks++; null }, // always discard
        )

        assertTrue(result.isEmpty())
        assertTrue(checks <= 3 + 1, "expected termination near N checks, got $checks")
    }

    @Test
    fun driverSinglePathUnrealizablePairIsAbandonedByLookback() {
        val sink2Root = mapOf(0 to intSet(1))
        val root2Source = mapOf(1 to intSet(2))
        val preds: (Int, (Int) -> Unit) -> Unit = predecessorsOf(0 to 1, 1 to 2)
        var checks = 0

        selectMethodTraces(
            methodCount = 100,
            sinkMethods = intSet(0),
            rootMethods = intSet(1),
            sourceMethods = intSet(2),
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            forEachPredecessor = preds,
            cap = Int.MAX_VALUE,
            collect = { checks++; null },
        )

        assertTrue(checks <= 4, "lookback should abandon quickly, not spin to the N-cap; got $checks")
    }

    @Test
    fun driverAlternatingUnrealizablePathsFallThroughToNCap() {
        val sink2Root = mapOf(0 to intSet(1, 2), 1 to intSet(3), 2 to intSet(3))
        val root2Source = mapOf(3 to intSet(4))
        val preds: (Int, (Int) -> Unit) -> Unit =
            predecessorsOf(0 to 1, 0 to 2, 1 to 3, 2 to 3, 3 to 4)
        val methodCount = 5
        var checks = 0

        val result = selectMethodTraces(
            methodCount = methodCount,
            sinkMethods = intSet(0),
            rootMethods = intSet(3),
            sourceMethods = intSet(4),
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            forEachPredecessor = preds,
            cap = Int.MAX_VALUE,
            collect = { checks++; null },
        )

        assertTrue(result.isEmpty())
        // More than the 2 checks a single-path pair takes (alternation defeats the immediate
        // lookback), and bounded by the N-cap so it still terminates.
        assertTrue(checks >= 3, "alternation should defeat the 1-step lookback; got $checks")
        assertTrue(checks <= methodCount + 1, "must terminate via the N-cap; got $checks")
    }

    @Test
    fun driverRespectsCap() {
        // Two independent sinks, each with its own source.
        val sink2Root = mapOf(0 to intSet(2), 1 to intSet(3))
        val root2Source = mapOf(2 to intSet(4), 3 to intSet(5))
        val preds: (Int, (Int) -> Unit) -> Unit =
            predecessorsOf(0 to 2, 1 to 3, 2 to 4, 3 to 5)

        val result = selectMethodTraces(
            methodCount = 6,
            sinkMethods = intSet(0, 1),
            rootMethods = intSet(2, 3),
            sourceMethods = intSet(4, 5),
            sink2RootEdges = edgeFn(sink2Root),
            root2SourceEdges = edgeFn(root2Source),
            forEachPredecessor = preds,
            cap = 1,
            collect = { it },
        )

        assertEquals(1, result.size)
    }

    @Test
    fun allMethodTracesProducesACoveringTraceOnRealGraph() {
        val g = Source2SinkMethodTraceGraph()
        // register methods 0..2 densely
        val m = (0..2).map { g.getOrCreateMethodIdx(mockk<CommonMethod>()) }
        val sink = m[0]; val root = m[1]; val source = m[2]

        g.sinkMethods.add(sink)
        g.rootMethods.add(root)
        g.sourceMethods.add(source)
        g.sink2RootMethodEdges.computeIfAbsent(sink) { _ -> intSet() }.add(root)
        g.root2SinkMethodEdges.computeIfAbsent(root) { _ -> intSet() }.add(sink)
        g.root2SourceMethodEdges.computeIfAbsent(root) { _ -> intSet() }.add(source)
        g.source2RootMethodEdges.computeIfAbsent(source) { _ -> intSet() }.add(root)

        val traces = g.allMethodTraces(limit = null) { it }

        assertEquals(1, traces.size)
        assertEquals(listOf(sink, root), traces.single().sink2Root.toList())
        assertEquals(listOf(root, source), traces.single().root2Source.toList())
    }

    private fun predecessorsOf(vararg edges: Pair<Int, Int>): (Int, (Int) -> Unit) -> Unit {
        val preds = HashMap<Int, MutableList<Int>>()
        for ((from, to) in edges) preds.getOrPut(to) { mutableListOf() }.add(from)
        return { node, action -> preds[node]?.forEach(action) }
    }

    private fun intSet(vararg xs: Int) = IntOpenHashSet().apply { xs.forEach { add(it) } }

    private fun edgeFn(edges: Map<Int, IntOpenHashSet>): (Int) -> IntOpenHashSet? = { edges[it] }

    private fun recordingCollect(into: MutableList<Pair<List<Int>, List<Int>>>): (MethodTrace) -> MethodTrace? = { t ->
        into.add(t.sink2Root.toList() to t.root2Source.toList())
        t
    }
}
