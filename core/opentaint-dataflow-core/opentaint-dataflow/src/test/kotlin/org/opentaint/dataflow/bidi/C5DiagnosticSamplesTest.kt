package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.DemandQueryStatistics
import kotlin.test.*

class C5DiagnosticSamplesTest {
    @Test fun `copied row sample retains its exact budget and is bounded independently of counters`() {
        MethodAnalysisFixtures().use { fixture ->
            val stats = DemandQueryStatistics()
            val t = MarkSlot.Concrete(fixture.mark("T"))
            val p = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val path = listOf(fixture.field("a"), fixture.field("b"))
            val member = fixture.manager.initial(fixture.pattern(p, mark = t))
            val pair = DemandPattern(fixture.pattern(p, tail = Tail.ANY, mark = t),
                fixture.pattern(ret, tail = Tail.ANY, mark = t))
            val raw = fixture.fact(ret, path, mark = t)
            val output = fixture.fact(ret, path.take(1), Tail.ANY, t, layer = Layer.DEMAND)
            val row = assertNotNull(stats.sampleRow(fixture.key, member, raw, pair, 1, 0))
            repeat(100) { stats.sampleResult(row, raw, output) }
            val snapshot = stats.rowSamples()
            assertEquals(64, snapshot.size)
            assertTrue(snapshot.all { "budget=1" in it && "maxFL2" in it && "/DEMAND/" in it })
            assertTrue("Dc=" in snapshot.first() && "Dp=" in snapshot.first())
            assertFalse("matchingMember" in stats.toString(), "Numeric counters remain a bounded line")
            stats.sampleResult(row, null, null)
            assertEquals(64, stats.rowSamples().size)
            assertTrue(stats.rowSamples().last().endsWith("selected=null admitted=null"))
            assertFalse(snapshot.last().endsWith("selected=null admitted=null"), "Snapshot owns copied strings")
        }
    }
}
