package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

class SelectedCallPolicyHelpersTest {
    @Test
    fun `persisted replay is per offer and current subscription never replays persisted records`() {
        for (run in listOf(3, 4)) PipelineFixtures(index = run).use { f ->
            val initial = f.ap.initial(f.store.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            f.records.add(Record(f.callee, Direction.FORWARD, initial,
                f.store.fact(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)))
            val actual = f.store.fact(
                base = if (run == 3) AccessPathBase.Argument(0) else AccessPathBase.Return,
                tail = Tail.EXACT, mark = MarkSlot.Concrete(f.store.mark("T")))
            val part = f.subscription(actual)
            assertTrue(emitRestrictedInitials(f.config, f.ops, f.callee, actual).isEmpty())
            repeat(2) { f.replayPersisted(part) }
            assertEquals(2, f.native.size + f.views.size)
            assertTrue(f.storages.isEmpty(), "Saved replay must not obtain live summary storage")
            f.subscriptions.subscribe(part)
            f.subscriptions.subscribe(part)
            assertEquals(2, f.native.size + f.views.size, "Live replay must not replay records again")
        }
    }

    @Test
    fun `aggregate counters separate saved offers from empty and eligible demand lookups`() {
        PipelineFixtures(index = 3).use { f ->
            val initial = f.ap.initial(f.store.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            f.records.add(Record(f.callee, Direction.FORWARD, initial,
                f.store.fact(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)))
            val actual = f.store.fact(path = listOf(f.store.field("f")),
                mark = MarkSlot.Concrete(f.store.mark("T")))
            val part = f.subscription(actual)
            val statistics = N2Statistics()
            repeat(2) {
                replayPersistedSummaries(f.config, f.ops, part, f.port.applier(part.caller), statistics)
            }
            assertTrue(emitRestrictedInitials(f.config, f.ops, f.callee, actual, statistics).isEmpty())
            val demand = DemandStore.Builder(f.ap).apply {
                add(f.callee, DemandPattern(f.store.pattern(tail = Tail.ANY, mark = MarkSlot.STAR), null))
            }.build()
            val eligible = f.method.config(index = 3, demand = demand)
            assertEquals(1, emitRestrictedInitials(eligible, f.ops, f.callee, actual, statistics).size)
            val snapshot = statistics.snapshot()
            assertEquals(2L, snapshot.persistedReplayInvocations)
            assertEquals(2L, snapshot.persistedReplayCandidates)
            assertEquals(2L, snapshot.persistedReplayMatches)
            assertEquals(2L, snapshot.demandLookupInvocations)
            assertEquals(1L, snapshot.demandLookupEmpty)
            assertEquals(1L, snapshot.demandLookupEligible)
            assertEquals(0L, snapshot.initialPackets, "A query alone sends no initial packet")
            assertEquals(0L, snapshot.acceptedDeltas, "A saved replay does not admit live input")
        }
    }

    @Test
    fun `completed emission retains shared initial identity without replacing actual caller paths`() {
        MethodAnalysisFixtures().use { f ->
            val field = f.field("f")
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR), null))
            }.build()
            val config = f.config(index = 3, demand = demand)
            val actuals = listOf("a" to "T", "b" to "U").map { (child, mark) ->
                f.fact(path = listOf(field, f.field(child)), tail = Tail.EXACT,
                    mark = MarkSlot.Concrete(f.mark(mark)))
            }
            val answers = actuals.map { emitRestrictedInitials(config, f.ops, f.key, it).single() }
            assertSame(answers[0], answers[1])
            assertEquals(listOf(field), answers[0].pathArray.asList())
            assertEquals(Tail.STAR, answers[0].tail)
            assertEquals(MarkSlot.STAR, answers[0].mark)
            assertNotEquals(actuals[0], actuals[1])
        }
    }

    @Test
    fun `moved complete query equals receiver query across restricted tails marks exclusions and layers`() {
        MethodAnalysisFixtures().use { f ->
            val field = f.field("f")
            val child = f.field("g")
            val blocked = f.field("blocked")
            val t = f.mark("T")
            val u = f.mark("U")
            val tails = listOf(Tail.STAR, Tail.EXACT, Tail.ANY, Tail.ANY_TAINT)
            val marks = listOf(MarkSlot.STAR, MarkSlot.Concrete(t), MarkSlot.Concrete(u))
            val exclusions = listOf(ExclusionSet.Empty, ExclusionSet.of(blocked))
            var cases = 0
            for (run in 2..5) {
                val demand = DemandStore.Builder(f.manager).apply {
                    for (tail in tails) for (mark in marks) for (path in listOf(emptyList(), listOf(field))) {
                        if (tail == Tail.ANY_TAINT) continue
                        if (mark is MarkSlot.Star && tail != Tail.ANY && !(run == 2 && tail == Tail.STAR)) continue
                        add(f.key, DemandPattern(f.pattern(path = path, tail = tail, mark = mark), null))
                    }
                }.build()
                val config = f.config(index = run, demand = demand)
                for (tail in tails) for (mark in marks) for (e in exclusions)
                    for (layer in Layer.entries) for (path in listOf(emptyList(), listOf(field), listOf(field, child))) {
                        // Only STAR and MUST carry field exclusions in the submitted grammar.
                        if (e != ExclusionSet.Empty && tail !in listOf(Tail.STAR, Tail.ANY_TAINT)) continue
                        val actual = f.fact(path = path, tail = tail, mark = mark, exclusion = e, layer = layer)
                        val reference = LinkedHashSet<InitialAp>()
                        f.ops.limit(actual, config.fieldLimit, object : ApOut {
                            override fun markRequest(mark: TaintMark): Nothing = error("Unexpected field-cut request")
                            override fun result(facts: Facts) {
                                // This is the receiver's original complete-query boundary.
                                for (leaf in f.ops.leaves(facts)) {
                                    f.cancellation.checkpoint()
                                    if (run == 2) validateRun2StaticFullInput(f.manager, leaf, config.fieldLimit)
                                }
                                reference.addAll(demand.initials(f.key, facts, config.admissionPolicy))
                            }
                        })
                        assertEquals(reference, emitRestrictedInitials(config, f.ops, f.key, actual).toSet(),
                            "run-$run $tail $mark $path $layer $e")
                        cases++
                    }
            }
            assertEquals(432, cases)
        }
    }

    @Test
    fun `concrete demand never admits a different concrete mark`() {
        MethodAnalysisFixtures().use { f ->
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(f.pattern(tail = Tail.ANY,
                    mark = MarkSlot.Concrete(f.mark("T"))), null))
            }.build()
            val config = f.config(index = 3, demand = demand)
            val actual = f.fact(path = listOf(f.field("f")), tail = Tail.EXACT,
                mark = MarkSlot.Concrete(f.mark("U")))
            assertTrue(emitRestrictedInitials(config, f.ops, f.key, actual).isEmpty())
        }
    }
}
