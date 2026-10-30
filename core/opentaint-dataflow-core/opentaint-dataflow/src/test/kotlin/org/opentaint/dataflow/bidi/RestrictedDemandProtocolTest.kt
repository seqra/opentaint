package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

/** Demand admits execution and paired publications. Actual input is not permission. */
class RestrictedDemandProtocolTest {
    private fun arrive(f: MethodAnalysisFixtures, actor: RunMethodAnalyzer, value: Facts) {
        f.submitRestricted(actor, value)
    }

    @Test fun `empty demand starts no nonzero initial in either restricted direction`() {
        for (index in listOf(2, 3)) MethodAnalysisFixtures().use { f ->
            val actor = f.core(index = index)
            arrive(f, actor, f.fact(mark = MarkSlot.Concrete(f.mark("T"))))
            assertEquals(0, actor.initials.all().size)
            assertFalse(actor.nonZeroInitial)
            assertTrue(f.processed.isEmpty())
        }
    }

    @Test fun `abstract entry shares one FLOW initial across actual marks and duplicate arrivals`() {
        for (index in listOf(2, 3)) MethodAnalysisFixtures().use { f ->
            val entry = f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR)
            val demand = DemandStore.Builder(f.manager).apply { add(f.key, DemandPattern(entry, null)) }.build()
            val actor = f.core(index = index, demand = demand)
            repeat(3) { for (name in listOf("T", "U"))
                arrive(f, actor, f.fact(tail = Tail.ANY, mark = MarkSlot.Concrete(f.mark(name)), layer = Layer.DEMAND)) }
            assertEquals(1, actor.initials.all().size)
            assertTrue(actor.initials.all().contains(f.manager.initial(entry)))
        }
    }

    @Test fun `concrete entry does not obtain T from FLOW or a different concrete mark`() {
        MethodAnalysisFixtures().use { f ->
            val t = f.mark("T")
            val entry = f.pattern(tail = Tail.ANY, mark = MarkSlot.Concrete(t))
            val demand = DemandStore.Builder(f.manager).apply { add(f.key, DemandPattern(entry, null)) }.build()
            val actor = f.core(index = 2, demand = demand)
            arrive(f, actor, f.fact(tail = Tail.STAR, mark = MarkSlot.STAR))
            arrive(f, actor, f.fact(tail = Tail.STAR, mark = MarkSlot.Star(f.manager.markSetOf(f.mark("U")))))
            arrive(f, actor, f.fact(tail = Tail.ANY, mark = MarkSlot.Concrete(f.mark("U"))))
            assertEquals(0, actor.initials.all().size)
            arrive(f, actor, f.fact(tail = Tail.ANY, mark = MarkSlot.Concrete(t), layer = Layer.DEMAND))
            assertTrue(actor.initials.all().contains(f.manager.initial(entry)))
            assertEquals(1, actor.initials.all().size)
        }
    }

    @Test fun `ANY static concrete entry does not also start an EXACT query`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val entry = f.pattern(STATIC, path, Tail.ANY, MarkSlot.Concrete(f.mark("T")))
            val demand = DemandStore.Builder(f.manager).apply { add(f.key, DemandPattern(entry, null)) }.build()
            val actor = f.core(index = 2, demand = demand)
            arrive(f, actor, f.fact(STATIC, path, Tail.ANY, entry.fact.mark, layer = Layer.DEMAND))
            assertEquals(1, actor.initials.all().size)
            assertTrue(actor.initials.all().contains(f.manager.initial(entry)))
            assertFalse(actor.initials.all().contains(f.manager.initial(entry.copy(fact = entry.fact.copy(tail = Tail.EXACT)))))
        }
    }

    @Test fun `late input cannot republish a raw summary with no exit permission`() {
        MethodAnalysisFixtures().use { f ->
            val entry = f.pattern(mark = MarkSlot.Concrete(f.mark("T")))
            val demand = DemandStore.Builder(f.manager).apply { add(f.key, DemandPattern(entry, null)) }.build()
            val actor = f.core(index = 3, demand = demand)
            val initial = f.manager.initial(entry)
            val raw = f.fact(AccessPathBase.Return, mark = entry.fact.mark, layer = Layer.DEMAND)
            actor.summaryDelta(initial, raw)
            arrive(f, actor, f.fact(mark = entry.fact.mark))
            f.drain(actor)
            assertTrue(actor.summaries.all().any { it.first === initial && it.second == raw })
            assertTrue(f.publications.flatten().isEmpty())
            assertTrue(actor.summaries.demandEdges().none())
        }
    }

    @Test fun `whole member containment and exit mark gate control publication`() {
        MethodAnalysisFixtures().use { f ->
            val t = MarkSlot.Concrete(f.mark("T")); val u = MarkSlot.Concrete(f.mark("U"))
            val entry = f.pattern(mark = t)
            val exit = f.pattern(AccessPathBase.Return, tail = Tail.ANY, mark = t)
            val demand = DemandStore.Builder(f.manager).apply { add(f.key, DemandPattern(entry, exit)) }.build()
            val actor = f.core(index = 3, demand = demand)
            val initial = f.manager.initial(entry)
            actor.summaryDelta(initial, f.fact(AccessPathBase.Return, mark = u, layer = Layer.DEMAND))
            assertTrue(actor.summaries.demandEdges().none())
            actor.summaryDelta(initial, f.fact(AccessPathBase.Return, mark = t, layer = Layer.DEMAND))
            f.drain(actor)
            assertTrue(f.publications.flatten().any { it.premise === initial })
            assertTrue(f.publications.flatten().all { f.ops.leaves(it.conclusion).all { p -> p.fact.mark == t } })
        }
    }

    @Test fun `ND publication keeps all original premises after one member restriction`() {
        MethodAnalysisFixtures().use { f ->
            val mark = MarkSlot.Concrete(f.mark("T"))
            val left = f.manager.initial(f.pattern(AccessPathBase.Argument(0), mark = mark))
            val right = f.manager.initial(f.pattern(AccessPathBase.Argument(1), mark = mark))
            val original = f.manager.premiseOf(listOf(left, right))
            val exit = f.pattern(AccessPathBase.Return, tail = Tail.ANY, mark = mark)
            val demand = DemandStore.Builder(f.manager).apply { add(f.key, DemandPattern(left.toPattern(), exit)) }.build()
            val actor = f.core(index = 3, demand = demand)
            actor.summaryDelta(original, f.fact(AccessPathBase.Return, mark = mark))
            f.drain(actor)
            assertEquals(setOf(original), f.publications.flatten().map { it.premise }.toSet())
            assertTrue(f.publications.flatten().all { it.premise.size == 2 })
        }
    }

    @Test fun `run1 normal singleton stays raw and record eligible but is not selected demand`() {
        MethodAnalysisFixtures().use { f ->
            val actor = f.core()
            val initial = f.manager.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = MarkSlot.STAR))
            val raw = f.fact(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)
            actor.summaryDelta(initial, raw)
            f.drain(actor)
            assertEquals(listOf(initial to raw), actor.summaries.all().toList())
            assertTrue(actor.summaries.demandEdges().none())
            assertTrue(f.publications.flatten().isNotEmpty())
            f.records.persist(Direction.FORWARD, sequenceOf(f.key to actor.summaries))
            assertTrue(f.records.byEntry(f.key, initial.toPattern()).any())
        }
    }

    @Test fun `original backward ZERO seed return bypasses paired restriction only for ZERO original`() {
        MethodAnalysisFixtures().use { f ->
            val actor = f.core(index = 2)
            val result = f.fact(mark = MarkSlot.Concrete(f.mark("T")))
            actor.summaryDelta(f.manager.zero, result)
            actor.summaryDelta(f.manager.initial(f.pattern(mark = MarkSlot.Concrete(f.mark("U")))), result)
            f.drain(actor)
            assertEquals(setOf<PremiseKey>(f.manager.zero), f.publications.flatten().map { it.premise }.toSet())
        }
    }
}
