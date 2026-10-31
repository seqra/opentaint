package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Source discharge is terminal. Native reads use their existing matcher and create no source hit. */
class BackwardSourceSummaryTargetTest {
    private enum class Route { CURRENT, SAVED_BACKWARD, SAVED_FORWARD_VIEW }

    private fun plan(f: MethodAnalysisFixtures, callee: MethodKey) {
        val identity = StatementSummary.identities(setOf(AccessPathBase.Zero, AccessPathBase.Return,
            AccessPathBase.Argument(0), AccessPathBase.Argument(1)))
        f.call(1, CallPlan(identity.touched, listOf(
            CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN, identity),
            CallStage.Callees(CallPoint.BOUND, CallPoint.RETURNED, listOf(callee)),
            CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK, identity),
        ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
    }

    private fun demand(f: MethodAnalysisFixtures, original: PremiseKey): DemandStore =
        DemandStore.Builder(f.manager).apply {
            if (original.isZero) add(f.key, PairedDemand(DemandEntry.Target, DemandExit.Zero))
            else for (member in original.members) add(f.key,
                PairedDemand(DemandEntry.Data(member.toPattern()), DemandExit.Zero))
        }.build()

    @Test fun `all three backward source-summary routes emit one terminal with the complete caller original`() {
        for (route in Route.entries) for (tail in listOf(Tail.EXACT, Tail.ANY))
            for (originKind in listOf("zero", "single", "union")) MethodAnalysisFixtures().use { f ->
                val callee = f.store.key("source")
                plan(f, callee)
                val mark = MarkSlot.Concrete(f.mark("source U"))
                val initial = f.manager.initial(f.pattern(AccessPathBase.Return, mark = mark))
                val left = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
                val right = f.manager.initial(f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("V"))))
                // A header-only boundary test also checks a full caller union;
                // it does not add ND data propagation to backward analysis.
                val original = when (originKind) {
                    "zero" -> f.manager.zero
                    "single" -> left
                    else -> f.manager.union(left, right)
                }
                when (route) {
                    Route.CURRENT -> Unit
                    Route.SAVED_BACKWARD -> f.records.add(Record(callee, Direction.BACKWARD, initial, Reach.NORMAL))
                    Route.SAVED_FORWARD_VIEW -> f.records.add(Record(callee, Direction.FORWARD, f.manager.zero,
                        f.fact(AccessPathBase.Return, mark = mark)))
                }
                val config = RunConfig(2, 1, demand(f, original), f.records, SeedIndex.EMPTY, listOf(f.key))
                val actor = f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
                val layer = if (tail == Tail.ANY) Layer.DEMAND else Layer.NORMAL
                val part = Subscription(callee, CallerRef(actor.key, original, Layer.NORMAL, f.inst(1), 1), layer,
                    f.fact(AccessPathBase.Return, tail = tail, mark = mark, layer = layer))
                if (route == Route.CURRENT) actor.applySummary(part, Publication(initial, Reach.NORMAL), 0)
                else replayPersistedSummaries(config, f.ops, part, actor)
                f.drain(actor)
                val expected = setOf(TargetSummary(original, Target.DemandTarget))
                assertEquals(expected, actor.targets, "$route/$tail/$originKind")
                assertEquals(expected, actor.outgoingTargets, "Ordinary paired C5 admits the terminal")
                assertEquals(if (route == Route.CURRENT) 0L else 1L, actor.recordCrossings)
                assertTrue(actor.summaries.all().none(), "A source discharge does not return an AP result")
                assertTrue(f.processed.isEmpty(), "No CFG edge is enqueued by the terminal")
                assertTrue(f.cuts.isEmpty(), "No call return or cleanup suffix executes")
                assertTrue(checkNotNull(actor.sourceHits).entries().none(), "Replay is not an actual reverse GEN hit")
                assertTrue(actor.sinkSeeds.isEmpty())
            }
    }

    @Test fun `unmatched marked input cannot discharge a backward source summary`() {
        for (route in Route.entries) MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("source")
            plan(f, callee)
            val mark = MarkSlot.Concrete(f.mark("source U"))
            val initial = f.manager.initial(f.pattern(AccessPathBase.Return, mark = mark))
            when (route) {
                Route.CURRENT -> Unit
                Route.SAVED_BACKWARD -> f.records.add(Record(callee, Direction.BACKWARD, initial, Reach.NORMAL))
                Route.SAVED_FORWARD_VIEW -> f.records.add(Record(callee, Direction.FORWARD, f.manager.zero,
                    f.fact(AccessPathBase.Return, mark = mark)))
            }
            val original = f.manager.initial(f.pattern())
            val config = RunConfig(2, 1, demand(f, original), f.records, SeedIndex.EMPTY, listOf(f.key))
            val actor = f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            val part = Subscription(callee, CallerRef(actor.key, original, Layer.NORMAL, f.inst(1), 1), Layer.NORMAL,
                f.fact(AccessPathBase.Return, mark = MarkSlot.Concrete(f.mark("other"))))
            if (route == Route.CURRENT) actor.applySummary(part, Publication(initial, Reach.NORMAL), 0)
            else replayPersistedSummaries(config, f.ops, part, actor)
            assertTrue(actor.targets.isEmpty())
            assertEquals(0L, actor.recordCrossings)
            assertTrue(f.processed.isEmpty() && f.cuts.isEmpty())
            assertTrue(checkNotNull(actor.sourceHits).entries().none())
        }
    }

    @Test fun `balanced backward ZERO identity keeps ordinary call result handling`() = MethodAnalysisFixtures().use { f ->
        val callee = f.store.key("control")
        plan(f, callee)
        val config = RunConfig(2, 1, demand(f, f.manager.zero), f.records, SeedIndex.EMPTY, listOf(f.key))
        val actor = f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
        val part = Subscription(callee, CallerRef(actor.key, f.manager.zero, Layer.NORMAL, f.inst(1), 1),
            Layer.NORMAL, Reach.NORMAL)
        actor.applySummary(part, Publication(f.manager.zero, Reach.NORMAL), 0)
        f.drain(actor)
        assertTrue(actor.targets.isEmpty())
        assertTrue(actor.summaries.all().any { (p, facts) -> p.isZero && facts == Reach.NORMAL })
        assertTrue(f.cuts.any { it.first == Cut.CALL }, "Control identity still executes the ordinary suffix")
    }

    @Test fun `forward saved source remains an ordinary marked result without a Source seed`() {
        for (direction in Direction.entries) MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("source")
            plan(f, callee)
            val mark = MarkSlot.Concrete(f.mark("source U"))
            val result = f.fact(AccessPathBase.Return, mark = mark)
            val record = if (direction == Direction.FORWARD)
                Record(callee, direction, f.manager.zero, result)
            else Record(callee, direction, f.manager.initial(f.pattern(AccessPathBase.Return, mark = mark)), Reach.NORMAL)
            f.records.add(record)
            val config = RunConfig(3, 2, DemandStore.Builder(f.manager).build(), f.records, SeedIndex.EMPTY, listOf(f.key))
            val actor = f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            val part = Subscription(callee, CallerRef(actor.key, f.manager.zero, Layer.NORMAL, f.inst(1), 1),
                Layer.NORMAL, Reach.NORMAL)
            replayPersistedSummaries(config, f.ops, part, actor)
            f.drain(actor)
            assertTrue(actor.targets.isEmpty())
            assertTrue(actor.summaries.all().any { (p, facts) -> p.isZero && facts == result }, "$direction")
            assertEquals(1L, actor.recordCrossings)
            assertTrue(f.cuts.any { it.first == Cut.CALL })
            assertNull(actor.sourceHits)
            assertEquals(0, config.seeds.size)
        }
    }
}
