package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.store.BlockScope
import kotlin.test.*

class LoopBlockCallSuffixWorkTest {
    @Test fun `late zero summary reserves child work when static cleaner output is already stored`() {
        // void m() { while (again()) { callee(); /* selected cleaner C.f/T */ } }
        // ZERO passes the call before its first real callee summary arrives.
        // The suffix then registers a static read but produces duplicate ZERO.
        val graph = listOf(listOf(1), listOf(2, 3), listOf(1), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 3).use { f ->
            val callee = f.store.key(context = "late zero callee")
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val mark = f.mark("T")
            val zeroKeep = StatementSummary.identities(listOf(org.opentaint.dataflow.ap.ifds.AccessPathBase.Zero))
            f.call(2, CallPlan(setOf(STATIC), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, zeroKeep),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN,
                    listOf(CleanStep.Clean(Cleaner(STATIC, f.manager.path(path), CleanReach.EXACT, mark)))),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, zeroKeep),
            ), emptyList(), BEFORE, AFTER))
            f.onSubscribe = {}
            f.onLink = {}
            val actor = f.core(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key),
                run1MarkMode = MarkMode.FULL),
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            actor.addRootZero()
            f.drain(actor, quantum = 1)
            val runtime = assertNotNull(actor.blockRuntime)
            runtime.requireIdle()
            val subscription = f.subscriptions.first { it.callee == callee && it.ref.premise.isZero }
            assertNotEquals(BlockScope.ROOT, subscription.ref.scope,
                "The call suffix must belong to the actual loop block")
            val child = runtime.state(subscription.ref.scope)
            assertTrue(child.edges.edgesAt(f.inst(2)).any { (original, facts) -> original.isZero && facts is Reach },
                "The ordinary zero pass has already stored the call's output")
            val service = assertNotNull(actor.runnerPort.staticService)
            assertEquals(0, service.statistics().readDescriptors)
            f.enqueued.clear()

            // This is the first delayed ZERO summary, not a repeated publication.
            // The real owner event applies the suffix while the method is idle.
            actor.applySummary(subscription, Publication(f.manager.zero, Reach.NORMAL), 0)
            assertTrue(child.hasLocalWork,
                "The static cleaner must leave its genuine MarkInput registration pending")
            assertTrue(f.enqueued.any { it === actor },
                "A static suffix effect needs counted method Work even when post-S output is a duplicate")
            f.drain(actor, quantum = 1)
            runtime.requireIdle()
            assertEquals(1, service.statistics().readDescriptors,
                "The queued work must commit the actual static registration")
            actor.freeze()
            assertNull(actor.blockRuntime)
        }
    }
}
