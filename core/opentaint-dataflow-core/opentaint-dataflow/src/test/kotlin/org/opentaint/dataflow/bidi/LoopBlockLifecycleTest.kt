package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import kotlin.test.*

class LoopBlockLifecycleTest {
    private val graph = listOf(listOf(1), listOf(2), listOf(2, 3), emptyList())

    @Test fun `frozen method gauges include all scoped caches and scalar stores without retaining child state`() {
        MethodAnalysisFixtures(graph, normalExit = 3, n2Statistics = N2Statistics()).use { f ->
            val actor = f.core()
            actor.addRootZero()
            actor.addInitial(f.manager.initial(f.run1Pattern()))
            f.drain(actor)
            val children = actor.joinedBlockStates().filter { it.first != BlockScope.ROOT }.map { it.second }
            assertTrue(children.isNotEmpty())
            val caches = children.mapNotNull { it.binding?.deliveryStatistics() }
            assertTrue(caches.sumOf { it.searches } > 0, "This control must use actual local CFG delivery")
            val rootCache = actor.context.delivery
            val expectedHits = rootCache.hits + caches.sumOf { it.hits }
            val expectedSearches = rootCache.searches + caches.sumOf { it.searches }
            val expectedVisited = rootCache.visitedNodes + caches.sumOf { it.visited }
            val expectedDestinations = rootCache.destinations + caches.sumOf { it.destinations }
            val expectedWidth = maxOf(rootCache.maxWidth, caches.maxOf { it.maxWidth })
            val completionSnapshots = actor.blockRuntime!!.completionScalarStatistics().toList()
            assertTrue(completionSnapshots.isNotEmpty(), "The control must include real composite completion storage")
            val snapshots = (listOf(actor) + children).mapNotNull { it.edges.scalarStatisticsSnapshot() } + completionSnapshots
            val compact = snapshots.sumOf { it.compactPoints }
            val full = snapshots.sumOf { it.fullPoints }
            val words = snapshots.sumOf { it.bitWords }
            val steps = actor.steps
            actor.freeze()
            assertEquals(expectedHits, actor.cfgDeliveryHits)
            assertEquals(expectedSearches, actor.cfgDeliverySearches)
            assertEquals(expectedVisited, actor.cfgDeliveryVisitedNodes)
            assertEquals(expectedDestinations, actor.cfgDeliveryDestinations)
            assertEquals(expectedWidth, actor.cfgDeliveryMaxWidth)
            val frozen = assertNotNull(actor.scalarIdentityStatistics)
            assertEquals(compact, frozen.compactPoints)
            assertEquals(full, frozen.fullPoints)
            assertEquals(words, frozen.bitWords)
            assertEquals(steps, actor.steps)
            val body = assertNotNull(actor.bodyWorkSnapshot)
            assertTrue(body.blockCandidatePackets > 0)
            assertEquals(body.candidatePackets, body.methodCandidatePackets + body.blockCandidatePackets,
                "Internal boundaries must not be presented as only public-method candidate work")
            assertNull(actor.blockRuntime)
            assertNull(actor.rootRouting)
            assertEquals(listOf(BlockScope.ROOT), actor.joinedBlockStates().map { it.first })
            assertTrue(actor.blockSummaries().any(), "Only the admitted scoped snapshots must remain")
            for (child in children) assertFailsWith<IllegalStateException> { child.edges }
        }
    }

    @Test fun `one child cleanup failure still releases every child and the original method`() {
        MethodAnalysisFixtures(graph, normalExit = 3).use { f ->
            val failure = AssertionError("local cleanup")
            val created = ArrayList<BlockRunState>()
            val released = ArrayList<BlockRunState>()
            val actor = f.core(localFactory = MethodLocalServicesFactory { state ->
                created += state
                val delegate = RunMethodLocalServices(state)
                object : MethodLocalServices by delegate {
                    override fun freeze() {
                        delegate.freeze()
                        released += state
                        if (state.binding != null) throw failure
                    }
                }
            })
            actor.addRootZero()
            f.drain(actor)
            assertTrue(created.size > 1)
            assertSame(failure, assertFailsWith<AssertionError> { actor.freeze() })
            assertEquals(created.toSet(), released.toSet())
            assertTrue(failure.suppressed.isEmpty(), "One shared failure must not suppress itself")
            assertNull(actor.blockRuntime)
            assertNull(actor.rootRouting)
            for (state in created) assertFailsWith<IllegalStateException> { state.edges }
            assertFailsWith<IllegalStateException> { actor.work(1) }
        }
    }
}
