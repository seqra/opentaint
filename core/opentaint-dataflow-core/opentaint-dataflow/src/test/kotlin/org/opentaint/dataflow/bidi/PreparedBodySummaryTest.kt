package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.MethodRootRouting
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.PortId
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.test.*

class PreparedBodySummaryTest {
    private fun withFixture(test: (MethodAnalysisFixtures, DemandStore, InitialAp, Facts) -> Unit) {
        MethodAnalysisFixtures(listOf(listOf(1), emptyList()), 1).use { f ->
            val x = AccessPathBase.Argument(0)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(f.pattern(x, tail = Tail.ANY, mark = MarkSlot.STAR),
                    f.pattern(AccessPathBase.Return, tail = Tail.ANY, mark = MarkSlot.STAR)))
            }.build()
            test(f, demand, f.manager.initial(f.pattern(x, mark = MarkSlot.STAR)),
                f.fact(AccessPathBase.Return, mark = MarkSlot.STAR))
        }
    }

    private fun routing(query: (PortId, PremiseKey, Facts) -> List<Facts>?) = object : MethodRootRouting {
        override fun start(node: CommonInst, original: InitialAp, value: Facts) = Unit
        override fun enter(node: CommonInst, original: PremiseKey, value: Facts) = Unit
        override fun successors(node: CommonInst, original: PremiseKey, value: Facts) = Unit
        override fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts) = query(exit, original, raw)
    }

    @Test fun `body publication queries the normalized pair and persists that same original`() =
        withFixture { f, demand, original, raw ->
            val actor = f.core(index = 3, L = 2, demand = demand)
            val normalized = normalizeFlowSummary(f.manager, original, raw)
            var calls = 0
            actor.rootRouting = routing { exit, premise, facts ->
                calls++
                assertEquals(PortId.ROOT_EXIT, exit)
                assertEquals(normalized.premise, premise)
                assertEquals(normalized.facts, facts)
                demand.intersect(f.key, premise, facts, actor.context.config.admissionPolicy)
            }
            actor.retainBlockSummary(PortId.ROOT_EXIT, original, raw)
            f.drain(actor)
            assertEquals(1, calls)
            assertEquals(setOf(normalized.premise), actor.summaries.all().map { it.first }.toSet())
            actor.freeze()
        }

    @Test fun `an exact empty prepared result does not fall back to native nonempty C5`() =
        withFixture { f, demand, original, raw ->
            val actor = f.core(index = 3, L = 2, demand = demand)
            val normalized = normalizeFlowSummary(f.manager, original, raw)
            assertTrue(demand.intersect(f.key, normalized.premise, normalized.facts,
                actor.context.config.admissionPolicy).isNotEmpty())
            actor.rootRouting = routing { _, _, _ -> emptyList() }
            actor.retainBlockSummary(PortId.ROOT_EXIT, original, raw)
            f.drain(actor)
            assertTrue(actor.summaries.all().none())
            actor.freeze()
        }

    @Test fun `unsupported prepared result delegates to the native normalized C5 query`() =
        withFixture { f, demand, original, raw ->
            val actor = f.core(index = 3, L = 2, demand = demand)
            val normalized = normalizeFlowSummary(f.manager, original, raw)
            val expected = demand.intersect(f.key, normalized.premise, normalized.facts,
                actor.context.config.admissionPolicy)
            var calls = 0
            actor.rootRouting = routing { _, _, _ -> calls++; null }
            actor.retainBlockSummary(PortId.ROOT_EXIT, original, raw)
            f.drain(actor)
            assertEquals(1, calls)
            assertEquals(expected, actor.summaries.all().map { it.second }.toList())
            actor.freeze()
        }
}
