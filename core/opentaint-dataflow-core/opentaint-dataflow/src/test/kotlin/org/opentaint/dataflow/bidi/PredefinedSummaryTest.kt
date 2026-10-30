package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*

class PredefinedSummaryTest {
    private val f = StoreFixtures()
    private val registry = ClassStaticAccessor("Registry")
    private val cls = f.manager.accessors.index(registry)
    private val other = f.manager.accessors.index(ClassStaticAccessor("Other"))
    private val field = f.field("bean")
    private val child = f.field("child")
    private val model = CompleteMethodSummary(listOf(SummarySchema.ZeroIdentity,
        SummarySchema.PrefixFlowIdentity(STATIC, listOf(registry))), touched = setOf(STATIC))

    private fun apply(input: Facts, run1: Boolean = false, backward: Boolean = false): List<Facts> {
        val compiled = model.compile(f.manager).let { if (backward) it.reversed() else it }
        val out = CollectingOut()
        for (edge in compiled.edges) f.ops.applyEdge(input, f.manager.zero, edge.edge, statementEdge = false,
            mode = ApMode(run1, if (backward) Direction.BACKWARD else Direction.FORWARD,
                fieldLimit = 4, markMode = MarkMode.FULL), out = out)
        assertTrue(out.markRequests.isEmpty())
        return out.results
    }

    @Test fun `registry filter keeps exact descendant geometry layers exclusions and protection in both directions`() {
        for (backward in listOf(false, true)) for (layer in Layer.entries) {
            val input = f.fact(STATIC, listOf(cls, field, child), Tail.STAR,
                exclusion = ExclusionSet.of(f.field("excluded")), layer = layer) as TaintTree
            val protected = input.withProtection(input.root)
            val actual = apply(protected, backward = backward).single() as TaintTree
            assertEquals(input, actual)
            assertEquals(protected.nonSubsumable, actual.nonSubsumable)
            assertEquals(input.exclusion, actual.exclusion)
            assertEquals(layer, actual.layer)
            assertTrue(apply(f.fact(STATIC, listOf(other, field), layer = layer), backward = backward).isEmpty())
        }
    }

    @Test fun `ZERO has only its explicit control row and never seeds registry facts`() {
        for (backward in listOf(false, true)) for (layer in Layer.entries)
            assertEquals(listOf(Reach.of(layer)), apply(Reach.of(layer), backward = backward))
    }

    @Test fun `broad flow projection respects the registry exclusion`() {
        for (backward in listOf(false, true)) {
            val blocked = f.fact(STATIC, tail = Tail.STAR, mark = MarkSlot.STAR,
                exclusion = ExclusionSet.of(cls))
            assertTrue(apply(blocked, backward = backward).isEmpty())
            val input = f.fact(STATIC, tail = Tail.STAR, mark = MarkSlot.STAR)
            val output = apply(input, backward = backward).single()
            assertEquals(listOf(cls), f.ops.leaves(output).single().fact.path)
        }
    }

    @Test fun `run1 predefined stage routes registry result to exit as demand without a writer`() {
        MethodAnalysisFixtures().use { m ->
            val compiled = model.compile(m.manager)
            m.call(1, CallPlan(setOf(STATIC), listOf(CallStage.Predefined(CallPoint.BEFORE, CallPoint.AFTER,
                m.key.method, model, compiled)), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            lateinit var calls: RunMethodCallServices
            val core = m.core(localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory { RunMethodCallServices(it).also { calls = it } })
            val initial = m.manager.initial(m.store.pattern(AccessPathBase.Argument(0), tail = Tail.STAR, mark = MarkSlot.STAR))
            val path = listOf(m.manager.accessors.index(registry), m.store.field("bean"))
            val input = m.store.fact(STATIC, path, Tail.STAR, mark = MarkSlot.STAR)
            calls.process(EdgeDelta(initial, m.inst(1), input))
            val result = core.edges.edgesAt(m.inst(1), initial).single().second
            assertEquals(Layer.DEMAND, result.layer)
            assertTrue(core.edges.edgesAt(m.inst(2), initial).none(), "Static shortcut queues the exit input without pre-storing it")
            m.drain(core)
            assertTrue(core.edges.edgesAt(m.inst(2), initial).any { it.second.layer == Layer.DEMAND },
                "Exit processing stores the completed DEMAND result")
            assertTrue(m.subscriptions.isEmpty())
            assertTrue(m.sentLinks.isEmpty())
            assertTrue(m.events.none { it is RunEvent.StaticOwner })
        }
        assertTrue(apply(f.fact(STATIC, listOf(other), Tail.EXACT), run1 = true).isEmpty())
    }

    @Test fun `complete empty model closes implicit ZERO call bypass and creates no subscriptions`() {
        MethodAnalysisFixtures().use { m ->
            val empty = CompleteMethodSummary(emptyList(), touched = setOf(STATIC))
            val plan = CallPlan(setOf(STATIC), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.ADDED, StageKind.BIND_IN,
                    MicroEdgeBuilder().apply { keepZero() }.buildStage()),
                CallStage.Predefined(CallPoint.ADDED, CallPoint.AFTER, m.key.method, empty, empty.compile(m.manager)),
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER, zeroCanReturn = false)
            m.call(1, plan)
            lateinit var calls: RunMethodCallServices
            val core = m.core(localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory { RunMethodCallServices(it).also { calls = it } })
            calls.process(EdgeDelta(m.manager.zero, m.inst(1), Reach.of(Layer.NORMAL)))
            assertTrue(core.edges.edgesAt(m.inst(1), m.manager.zero).none(), "An empty complete model has no call output")
            assertTrue(core.edges.edgesAt(m.inst(2), m.manager.zero).none())
            assertTrue(m.subscriptions.isEmpty())
            assertTrue(m.sentLinks.isEmpty())
        }
    }

    @Test fun `reversed call-site source retains T to ZERO dependency without a body control row`() {
        MethodAnalysisFixtures().use { m ->
            val x = AccessPathBase.Argument(0)
            val empty = CompleteMethodSummary(emptyList(), touched = setOf(STATIC))
            val assigned = m.store.pattern(x).fact
            val plan = CallPlan(setOf(STATIC, x), listOf(
                CallStage.Edges(CallPoint.BEFORE, CallPoint.BOUND, StageKind.BIND_IN,
                    MicroEdgeBuilder().apply { keepZero() }.buildStage()),
                CallStage.Edges(CallPoint.BOUND, CallPoint.REWRITTEN, StageKind.SOURCES,
                    MicroEdgeBuilder().apply { edge(PathEdge(ZERO_FACT, assigned, ExclusionSet.Empty)) }.buildStage()),
                CallStage.Actions(CallPoint.BOUND, CallPoint.ADDED, emptyList()),
                CallStage.Predefined(CallPoint.ADDED, CallPoint.RETURNED, m.key.method, empty, empty.compile(m.manager)),
                CallStage.Actions(CallPoint.RETURNED, CallPoint.REWRITTEN, emptyList()),
                CallStage.Edges(CallPoint.REWRITTEN, CallPoint.AFTER, StageKind.BIND_BACK,
                    StatementSummary.identities(listOf(x))),
            ), emptyList(), CallPoint.BEFORE, CallPoint.AFTER, zeroCanReturn = false)
            m.call(1, plan)
            lateinit var calls: RunMethodCallServices
            val core = m.core(index = 2, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory { RunMethodCallServices(it).also { calls = it } })
            val initial = m.manager.initial(m.store.pattern(x))
            calls.process(EdgeDelta(initial, m.inst(1), m.store.fact(x)))
            assertTrue(core.edges.edgesAt(m.inst(1), initial).any { it.second is Reach },
                "The reversed source result is stored under its call statement")
            assertTrue(core.edges.edgesAt(m.inst(0), initial).none(), "The predecessor input has not executed")
            m.drain(core)
            assertTrue(core.edges.edgesAt(m.inst(0), initial).any { it.second is Reach },
                "The reversed source dependency completes at the method entry boundary")
            assertTrue(m.subscriptions.isEmpty())
            assertTrue(m.sentLinks.isEmpty())
        }
    }

    @Test fun `immutable model owns its rows and unsupported exceptional lane is rejected`() {
        val rows = arrayListOf<SummarySchema>(SummarySchema.ZeroIdentity)
        val touched = linkedSetOf(STATIC)
        val owned = CompleteMethodSummary(rows, touched = touched)
        rows.clear(); touched.clear()
        assertTrue(owned.zeroCanReturn)
        assertEquals(setOf(STATIC), owned.touched)
        assertFails { (owned.normal as MutableList).clear() }
        assertFailsWith<IllegalArgumentException> {
            CompleteMethodSummary(emptyList(), listOf(SummarySchema.ZeroIdentity), setOf(STATIC))
        }
    }
}
