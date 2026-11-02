package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class LoopBlockSavedTargetWorkTest {
    @Test fun `saved local normal Target reserves work before empty current block admission returns`() {
        // void m(Node p) {
        //   sinkT(p); removeAllMarks(p);  // BL has a NORMAL Target, but no DATA output.
        //   while (again()) { }
        // }
        val graph = listOf(listOf(1), listOf(2), listOf(3), listOf(4, 5), listOf(3), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 5).use { f ->
            val p = AccessPathBase.Argument(0)
            val mark = MarkSlot.Concrete(f.mark("T"))
            val identity = StatementSummary.identities(listOf(p))
            val sink = localSink(listOf(f.pattern(p, mark = mark)))
            fun call(sinks: List<SinkRule> = emptyList(), cleanup: List<CleanStep> = emptyList()) =
                CallPlan(setOf(p), listOf(
                    CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
                    CallStage.Actions(BOUND, ADDED, emptyList()),
                    CallStage.Edges(ADDED, RETURNED, UNRESOLVED, identity),
                    CallStage.Actions(RETURNED, REWRITTEN, cleanup),
                    CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
                ), sinks, BEFORE, AFTER)
            f.call(1, call(sinks = listOf(sink)))
            f.call(2, call(cleanup = listOf(CleanStep.Clean(Cleaner(p, null, CleanReach.AT_AND_BELOW, null)))))
            val native = f.core(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL),
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            native.addInitial(f.manager.initial(f.pattern(p, tail = Tail.EXACT, mark = mark)))
            f.drain(native, quantum = 1)
            native.freeze()
            val layout = f.contexts.blockLayout(f.key)
            val before = checkNotNull(layout[layout.root].before)
            val local = native.blockTargets().filter { it.scope.block == before }.flatMap { owner ->
                owner.rows.asSequence().mapNotNull { row ->
                    (row.target as? Target.NormalTarget)?.let { OwnedNormalTarget(f.key, row.premise, it.id, owner.scope) }
                }
            }.toList()
            assertTrue(local.isNotEmpty(), "The actual prior sink must produce a scoped NORMAL Target")
            assertTrue(local.all { !it.premise.isZero }, "ZERO-to-NormalTarget replay is deliberately absent")
            assertTrue(native.blockSummaries().filter { it.key.scope.block == before }.all { it.summaries.all().none() },
                "The all-marks cleaner leaves no saved BL DATA transfer to provide a different wakeup")
            val public = native.targets.mapNotNull { row ->
                (row.target as? Target.NormalTarget)?.let { OwnedNormalTarget(f.key, row.premise, it.id) }
            }
            val saved = NormalTargetStore(f.manager, (public + local).asSequence())
            val incoming = f.pattern(p, tail = Tail.EXACT, mark = mark)
            val demand = DemandStore.Builder(f.manager).apply {
                // A legitimate public input permission. No local current demand
                // or DATA record is added to make the saved-only replay run.
                add(f.key, DemandPattern(incoming, f.manager.zero.toPattern()))
            }.build()
            val config = RunConfig(3, 2, demand, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL, normalTargets = saved)
            val actual = f.manager.factsOf(incoming.fact, ExclusionSet.Empty, Layer.NORMAL)
            val admitted = demand.initials(f.key, actual, config.admissionPolicy).single()
            assertEquals(Layer.NORMAL, admitted.layer)
            assertTrue(local.any { saved.candidates(f.key, it.scope, admitted.initial, actual, config.mode).isNotEmpty() },
                "The genuine saved nonzero NORMAL row must match the provided NORMAL input")
            f.processed.clear()
            f.enqueued.clear()
            val actor = f.core(config,
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            actor.addInitial(admitted)
            assertTrue(f.enqueued.any { it === actor },
                "A saved Target-only replay needs counted root Work even when C2 admits no local initial")
            f.drain(actor, quantum = 1)
            assertNotNull(actor.blockRuntime).requireIdle()
            assertTrue(local.all { saved.contains(f.key, admitted.initial, it.id) },
                "The complete saved store retains the genuine public NORMAL identity")
            assertTrue(actor.targets.none { row -> row.target is Target.NormalTarget },
                "A persisted public NORMAL Target must suppress its repeated fresh publication")
            assertEquals(listOf(BlockScope.ROOT), actor.joinedBlockStates().map { it.first },
                "Saved-only terminal replay must not seed or analyze a local block")
            assertTrue(f.processed.isEmpty(), "No current physical instruction is needed for saved Target replay")
            actor.freeze()
        }
    }
}
