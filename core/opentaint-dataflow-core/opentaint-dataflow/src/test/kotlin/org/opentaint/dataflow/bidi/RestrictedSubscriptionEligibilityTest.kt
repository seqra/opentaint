package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

/** Controls for restricted admission and canonical initial-key delivery. */
class RestrictedSubscriptionEligibilityTest {
    @Test
    fun `two branch writes with empty demand create no live subscription or raw input`() {
        MethodAnalysisFixtures(successors = listOf(listOf(1, 2), listOf(3), listOf(3), listOf(4), emptyList()),
            normalExit = 4).use { f ->
            val p = AccessPathBase.Argument(0)
            // Both branches overwrite p.f. An exact mark at p survives either write.
            val field = f.field("f")
            val identity = PathFact(p, emptyList(), Tail.STAR, MarkSlot.STAR)
            val write = StatementSummary(setOf(p), listOf(MicroEdge.of(
                PathEdge(identity, identity, ExclusionSet.of(field)))), emptyList(), emptyMap())
            f.statement(1, write)
            f.statement(2, write)
            val callee = f.store.key("callee")
            f.call(3, CallPlan(setOf(p), listOf(
                CallStage.Callees(CallPoint.ADDED, CallPoint.AFTER, listOf(callee))),
                emptyList(), CallPoint.ADDED, CallPoint.AFTER))
            val directory = CalleeSubscriptions(f.ops)
            var fresh = 0
            f.onSubscribe = { if (directory.add(it) != null) fresh++ }
            f.onLink = { }
            val actor = f.core(index = 3, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            actor.addInitial(f.manager.initial(f.pattern(tail = Tail.EXACT,
                mark = MarkSlot.Concrete(f.mark("T")))))
            f.drain(actor)
            assertTrue(f.subscriptions.isEmpty())
            assertEquals(0, fresh)
            assertTrue(f.sentLinks.isEmpty())
            assertTrue(f.sentInitials.isEmpty())
            // No callee reply exists yet. No completed output at the call can gate these inputs.
            assertTrue(actor.edges.edgesAt(f.inst(3)).none())
            directory.clear()
        }
    }

    @Test
    fun `different actual paths and marks can start the same canonical initial`() {
        MethodAnalysisFixtures().use { f ->
            val field = f.field("f")
            val entry = f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(entry, null))
            }.build()
            val policy = demand.admissionPolicy(3, 2, Direction.FORWARD)
            val actuals = listOf("a" to "T", "b" to "U").map { (child, mark) ->
                f.fact(path = listOf(field, f.field(child)), tail = Tail.EXACT,
                    mark = MarkSlot.Concrete(f.mark(mark)))
            }
            val emitted = actuals.map { demand.initials(f.key, it, policy).single() }
            assertSame(emitted[0], emitted[1])
            assertEquals(listOf(field), emitted[0].pathArray.asList())
            assertEquals(Tail.STAR, emitted[0].tail)
            assertEquals(MarkSlot.STAR, emitted[0].mark)
            val summary = f.fact(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)
            for (actual in actuals) {
                val out = CollectingOut()
                f.ops.applySummary(actual, emitted[0], summary, ApMode(false, Direction.FORWARD, 2), out)
                val answer = out.results.flatMap { f.ops.leaves(it).toList() }.single()
                val source = f.ops.leaves(actual).single()
                assertEquals(source.fact.path.drop(1), answer.fact.path)
                assertEquals(source.fact.mark, answer.fact.mark)
            }
        }
    }

    @Test
    fun `normalized publication applicability does not establish current demand admission`() {
        MethodAnalysisFixtures().use { f ->
            val entry = f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR)
            val exit = f.pattern(AccessPathBase.Return, tail = Tail.ANY, mark = MarkSlot.STAR)
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(entry, exit))
            }.build()
            val policy = demand.admissionPolicy(3, 2, Direction.FORWARD)
            val exactInput = f.fact(tail = Tail.EXACT, mark = MarkSlot.Concrete(f.mark("T")))
            val exactInitial = demand.initials(f.key, exactInput, policy).single()
            assertEquals(Tail.EXACT, exactInitial.tail)
            val raw = f.fact(AccessPathBase.Return, tail = Tail.EXACT, mark = MarkSlot.STAR)
            val normalized = normalizeFlowSummary(f.manager, exactInitial, raw)
            val pub = Publication(normalized.premise,
                demand.intersect(f.key, normalized.premise, normalized.facts, policy).single())
            assertEquals(Tail.STAR, (pub.premise as InitialAp).tail)

            val broad = f.fact(tail = Tail.STAR, mark = MarkSlot.STAR)
            assertTrue(demand.initials(f.key, broad, policy).isEmpty())
            val sub = Subscription(f.key,
                org.opentaint.dataflow.bidi.store.CallerRef(f.store.key("caller"), f.manager.zero,
                    Layer.NORMAL, f.inst(1)), broad.layer, broad)
            assertNotNull(matches(sub, pub, 0, f.ops, ApMode(false, Direction.FORWARD, 2)))
            // Applicability alone does not authorize replay or subscription.
            // The selected call policy applies persisted records first, then skips
            // current-run work when demand admission is empty. This control is
            // not a counterexample to that policy.
        }
    }

    @Test
    fun `empty demand does not remove native or reversed normal record replay`() {
        for (run in listOf(3, 4)) PipelineFixtures(index = run).use { f ->
            val initial = f.ap.initial(f.store.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            f.records.add(Record(f.callee, Direction.FORWARD, initial,
                f.store.fact(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)))
            val actual = f.store.fact(
                base = if (run == 3) AccessPathBase.Argument(0) else AccessPathBase.Return,
                tail = Tail.EXACT, mark = MarkSlot.Concrete(f.store.mark("T")))
            assertTrue(checkNotNull(f.config.demand).initials(f.callee, actual, f.config.admissionPolicy).isEmpty())
            f.replayPersisted(f.subscription(actual))
            if (run == 3) assertEquals(1, f.native.size)
            else assertTrue(f.views.isNotEmpty())
        }
    }

    @Test
    fun `initial admission occurs before there is a post-statement entry row`() {
        MethodAnalysisFixtures().use { f ->
            val actor = f.core(index = 3)
            val initial = f.manager.initial(f.pattern(tail = Tail.EXACT,
                mark = MarkSlot.Concrete(f.mark("T"))))
            actor.addInitial(initial)
            assertTrue(actor.edges.edgesAt(f.inst(0)).none())
            val boundaryWork = f.cuts.size
            assertTrue(boundaryWork > 0)
            actor.addInitial(initial)
            assertEquals(boundaryWork, f.cuts.size)
            assertEquals(listOf(initial), actor.initials.all().toList())
        }
    }
}
