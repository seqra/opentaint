package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.MicroEdgeBuilder
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

/** Exercise fixed-demand admission and publication through the actual method owner. */
class RestrictedDemandPipelineTest {
    private val arg = AccessPathBase.Argument(0)
    private val ret = AccessPathBase.Return

    private fun method(): MethodAnalysisFixtures = MethodAnalysisFixtures().also { f ->
        f.statement(1, MicroEdgeBuilder().apply { move(ret, arg) }.build())
    }

    private fun ref(f: MethodAnalysisFixtures): CallerRef =
        CallerRef(f.store.key("caller"), f.manager.zero, Layer.NORMAL, f.inst(1))

    @Test fun `later actual input with no guide cannot start a body or publish a response`() {
        method().use { f ->
            val t = f.mark("T")
            val input = f.fact(arg, mark = MarkSlot.Concrete(t))
            val actor = f.core(index = 3,
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            assertTrue(actor.initials.all().isEmpty())
            assertTrue(actor.summaries.all().none())
            f.admit(actor, ref(f), input.layer, input)
            assertTrue(actor.initials.all().isEmpty())
            f.drain(actor)
            assertTrue(f.publications.flatten().isEmpty())
            assertTrue(actor.summaries.all().none())
        }
    }

    @Test fun `actual input after a raw computation cannot change fixed exit permission`() {
        method().use { f ->
            val t = f.mark("T")
            val actual = f.manager.initial(f.pattern(arg, mark = MarkSlot.Concrete(t)))
            val actor = f.core(index = 3,
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            // A prior guide may have started the identical canonical assumption.
            actor.addInitial(actual)
            f.drain(actor)
            val expected = f.pattern(ret, mark = MarkSlot.Concrete(t))
            assertTrue(actor.summaries.all().any { (_, facts) -> expected in f.ops.leaves(facts).toList() })
            assertTrue(f.publications.isEmpty(), "No prior/current exit permission existed yet")
            val processed = actor.steps
            val input = f.fact(arg, mark = MarkSlot.Concrete(t))
            f.admit(actor, ref(f), input.layer, input)
            f.drain(actor)
            assertEquals(processed, actor.steps, "Raw response replay does not rerun the initial")
            assertTrue(f.publications.flatten().isEmpty(), "Later input cannot authorize an old raw answer")
        }
    }

    @Test fun `nonreturning demanded initial has no manufactured answer`() {
        MethodAnalysisFixtures(successors = listOf(listOf(1), listOf(1), emptyList()), normalExit = 2).use { f ->
            val input = f.fact()
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(f.ops.leaves(input).single(), f.pattern(ret, tail = Tail.ANY)))
            }.build()
            val actor = f.core(index = 3, demand = demand,
                localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            f.admit(actor, ref(f), input.layer, input)
            f.drain(actor)
            assertTrue(actor.nonZeroInitial)
            assertTrue(actor.summaries.all().none())
            assertTrue(f.publications.isEmpty())
        }
    }
}
