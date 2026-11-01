package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.BodyWorkStatistics
import org.opentaint.dataflow.bidi.engine.diagnosticComponents
import org.opentaint.dataflow.bidi.fixtures.testApManager
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.util.Cancellation
import java.util.BitSet
import kotlin.test.*

class BodyWorkStatisticsTest {
    private fun graph(next: List<List<Int>>) = CompactGraph.build(next.size) { index ->
        BitSet().apply { next[index].forEach(::set) }
    }

    @Test fun `SCC diagnostics match independent reachability on every three point CFG`() {
        for (mask in 0 until (1 shl 9)) {
            val next = List(3) { source -> (0..2).filter { mask and (1 shl (source * 3 + it)) != 0 } }
            fun reachable(start: Int): Set<Int> {
                val seen = mutableSetOf(start)
                do {
                    val old = seen.size
                    for (node in seen.toList()) seen += next[node]
                } while (seen.size != old)
                return seen
            }
            val reach = (0..2).map(::reachable)
            val (ids, cycles) = diagnosticComponents(graph(next))
            for (a in 0..2) for (b in 0..2)
                assertEquals(b in reach[a] && a in reach[b], ids[a] == ids[b])
            for (a in 0..2)
                assertEquals(next[a].any { a in reach[it] }, cycles[a])
        }
    }

    @Test fun `shared DAG counts path memberships and packed marks without scalar decoding`() {
        val cancellation = Cancellation()
        val ap = testApManager(cancellation)
        val f = ap.accessors.index(FieldAccessor("Box", "f", "Box"))
        val g = ap.accessors.index(FieldAccessor("Box", "g", "Box"))
        val t = ap.marks.mark("T")
        val u = ap.marks.mark("U")
        val leaf = ap.taintAlg.leafNode(ap.taintLeaves(MarkSet(intArrayOf(t.id, u.id)), MarkSet.EMPTY))
        val root = ap.taintAlg.node(TaintLeaves.EMPTY, intArrayOf(f, g).sortedArray(), arrayOf(leaf, leaf))
        val facts = ap.taintTree(AccessPathBase.Argument(0), Layer.NORMAL, root, nonSubsumable = root)
        val observer = BodyWorkStatistics(graph(listOf(listOf(1), listOf(1))), cancellation)
        observer.processed(1, ap.zero, facts)
        observer.fresh(1, ap.zero, facts)
        observer.candidate(ap.zero, facts)
        val before = observer.snapshot()
        assertEquals(listOf(1L, 1L, 1L), before.packets)
        assertEquals(listOf(4L, 4L, 4L), before.sampledMemberships)
        assertEquals(listOf(4L, 4L, 4L), before.sampledProtected)
        assertTrue(before.topPoints.first().cyclic)
        assertEquals(1L, before.cyclicProcessedPackets)
        assertEquals(1L, before.cyclicFreshPackets)
        assertEquals(1, before.samples.first().maxDepth)
        assertEquals(listOf(t.id, u.id), before.samples.first().exampleMarkIds.sorted())
        assertEquals(TaintMark.ZERO.id, before.samples.first().initials.single().concreteMark)
        observer.processed(0, ap.zero, facts)
        assertEquals(1L, before.processedPackets, "Snapshot has only copied scalar state")
        assertEquals(2L, observer.snapshot().processedPackets)
        assertEquals(1L, observer.snapshot().cyclicProcessedPackets)
        cancellation.cancel()
        assertEquals(1L, observer.candidatePackets)
        assertEquals(2L, observer.snapshot().processedPackets,
            "A stopped-owner diagnostic snapshot remains readable after cancellation")
    }

    @Test fun `sampling is periodic bounded and independent of exact packet counts`() {
        val cancellation = Cancellation()
        val ap = testApManager(cancellation)
        val observer = BodyWorkStatistics(graph(listOf(emptyList())), cancellation)
        repeat(70_000) { observer.processed(0, ap.zero, Reach.DEMAND) }
        val snapshot = observer.snapshot()
        assertEquals(70_000L, snapshot.processedPackets)
        assertEquals(16L + 70_000L / 1024L, snapshot.sampledPackets[0])
        assertEquals(64, snapshot.samples.size)
        assertEquals(0L, snapshot.droppedSamples)
        assertFalse(snapshot.topPoints.single().cyclic)
    }
}
