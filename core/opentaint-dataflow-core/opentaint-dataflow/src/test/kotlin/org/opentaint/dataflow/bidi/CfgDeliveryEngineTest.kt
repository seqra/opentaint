package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

class CfgDeliveryEngineTest {
    private val x = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return

    @Test fun `initial is input and completed results remain under their producer across neutral chain`() {
        MethodAnalysisFixtures(List(6) { if (it == 5) emptyList() else listOf(it + 1) }, normalExit = 5).use { f ->
            f.baseRelevance = { _, s, _, _ -> s.location.index == 0 || s.location.index == 4 }
            f.statement(4, MicroEdgeBuilder().apply { move(ret, x) }.build())
            val core = f.core()
            val initial = f.manager.initial(f.run1Pattern())
            core.addInitial(initial)
            assertTrue(core.edges.edgesAt(f.inst(0)).none(), "Entry has no completed result before it executes")
            f.drain(core, 1)
            assertEquals(listOf(0, 4, 5, 5), f.processed.map { it.node.location.index })
            assertTrue((1..3).all { core.edges.edgesAt(f.inst(it)).none() })
            assertEquals(setOf(x, ret), core.edges.edgesAt(f.inst(4)).map { it.second.base }.toSet())
            assertTrue(core.summaries.all().any { it.second.base == ret })
            val steps = core.steps
            core.emitUnchanged(f.processed.first())
            f.drain(core, 1)
            assertEquals(steps, core.steps, "A repeated producer identity never starts a new routing burst")
        }
    }

    @Test fun `diamond permits repeated relevant input but admits its output once`() {
        MethodAnalysisFixtures(listOf(listOf(1, 2), listOf(3), listOf(3), listOf(4), emptyList()), normalExit = 4).use { f ->
            // Each arm is relevant, so there are two independently fresh producers.
            val core = f.core()
            val initial = f.manager.initial(f.run1Pattern())
            core.addInitial(initial)
            f.drain(core, 1)
            assertEquals(2, f.processed.count { it.node.location.index == 3 })
            assertEquals(1, core.edges.edgesAt(f.inst(3), initial).count())
            assertEquals(1, f.processed.count { it.node.location.index == 4 })
        }
    }

    @Test fun `relevant identity loop terminates across quanta and retains protection upgrades`() {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(1, 2), emptyList())).use { f ->
            val core = f.core()
            val initial = f.manager.initial(f.run1Pattern())
            core.addInitial(initial)
            f.drain(core, 1)
            assertEquals(2, f.processed.count { it.node.location.index == 1 })
            val plain = f.run1Fact() as TaintTree
            core.emitAfter(initial, f.inst(1), plain.withProtection(plain.root))
            f.drain(core, 1)
            assertTrue(core.edges.edgesAt(f.inst(1), initial).map { it.second }.filterIsInstance<TaintTree>()
                .all { it.nonSubsumable != null })
            val steps = core.steps
            core.emitAfter(initial, f.inst(1), plain.withProtection(plain.root))
            f.drain(core, 1)
            assertEquals(steps, core.steps)
        }
    }

    @Test fun `closed neutral component has a cached empty frontier and no invented exit`() {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(1), emptyList())).use { f ->
            f.baseRelevance = { _, s, _, _ -> s.location.index == 0 }
            val core = f.core()
            core.addInitial(f.manager.initial(f.run1Pattern()))
            f.drain(core, 1)
            assertEquals(listOf(0), f.processed.map { it.node.location.index })
            assertTrue(core.summaries.all().none())
            assertTrue(core.context.delivery.targets(1, x).isEmpty())
            assertEquals(1L, core.context.delivery.hits)
        }
    }

    @Test fun `generic normal end still performs return transfer before boundary summary`() {
        MethodAnalysisFixtures().use { f ->
            f.statement(2, MicroEdgeBuilder().apply { move(ret, x) }.build())
            val core = f.core()
            core.addInitial(f.manager.initial(f.run1Pattern()))
            f.drain(core, 1)
            assertTrue(core.summaries.all().any { it.second.base == ret })
            assertTrue(core.edges.edgesAt(f.inst(2)).any { it.second.base == ret })
        }
    }
}
