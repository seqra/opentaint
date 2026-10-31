package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

/** Exercise real query, start and post-statement storage, not a second admission model. */
class InitialLayerDeliveryTest {
    @Test fun `both exact start lanes survive either arrival order and duplicate offers`() {
        for (order in listOf(Layer.entries, Layer.entries.reversed()))
            MethodAnalysisFixtures().use { f ->
                val entry = f.pattern()
                val initial = f.manager.initial(entry)
                val demand = DemandStore.Builder(f.manager).apply {
                    add(f.key, DemandPattern(entry, null))
                }.build()
                val actor = f.core(index = 3, demand = demand)
                for (layer in order) {
                    repeat(2) { f.submitRestricted(actor, f.fact(layer = layer)) }
                    f.drain(actor)
                }
                assertEquals(Layer.entries.map { AdmittedInitial(initial, it) }.toSet(),
                    actor.initials.admissions().toSet())
                val delivered = f.processed.filter { it.premise == initial && it.node == f.inst(1) }
                assertEquals(Layer.entries.toSet(), delivered.map { it.facts.layer }.toSet())
                assertEquals(2, delivered.size, "Each layer runs once at the statement")
            }
    }

    @Test fun `MAY offer starts exact DEMAND and later exact NORMAL discharges old guidance`() =
        MethodAnalysisFixtures().use { f ->
            val entry = f.pattern()
            val initial = f.manager.initial(entry)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(entry, null))
            }.build()
            val actor = f.core(index = 3, demand = demand)
            f.submitRestricted(actor, f.fact(tail = Tail.ANY, layer = Layer.DEMAND))
            f.drain(actor)
            assertEquals(listOf(AdmittedInitial(initial, Layer.DEMAND)), actor.initials.admissions())
            assertTrue(f.processed.filter { it.premise == initial }.all { it.facts.layer == Layer.DEMAND })
            f.submitRestricted(actor, f.fact())
            f.drain(actor)
            assertEquals(Layer.entries.toSet(), actor.initials.admissions().map { it.layer }.toSet())
        }

    @Test fun `intrinsic concrete STAR is canonical DEMAND before actor membership`() =
        MethodAnalysisFixtures().use { f ->
            val actor = f.core(index = 3)
            val initial = f.manager.initial(f.pattern(tail = Tail.STAR))
            for (layer in Layer.entries) actor.addInitial(AdmittedInitial(initial, layer))
            f.drain(actor)
            assertEquals(listOf(AdmittedInitial(initial, Layer.DEMAND)), actor.initials.admissions())
            assertTrue(f.processed.filter { it.premise == initial }.all { it.facts.layer == Layer.DEMAND })
        }
}
