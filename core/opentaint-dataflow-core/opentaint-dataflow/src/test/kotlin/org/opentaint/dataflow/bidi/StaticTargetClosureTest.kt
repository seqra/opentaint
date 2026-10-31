package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.HandOff
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

/** Run-1 static completion supplies complete typed pairs; it does not weaken C5. */
class StaticTargetClosureTest {
    private class Fixture {
        val f = EngineShellFixtures()
        val ap = f.manager
        val cls = ap.accessors.index(ClassStaticAccessor("C"))
        val fields = (0..3).map { f.field("f$it") }
        val t = MarkSlot.Concrete(ap.marks.mark("T"))
        val u = MarkSlot.Concrete(ap.marks.mark("U"))
        val v = MarkSlot.Concrete(ap.marks.mark("V"))
        val zero = ap.zero.toPattern()
        val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)
        fun c(index: Int, mark: MarkSlot = t, tail: Tail = Tail.STAR) =
            Pattern(PathFact(STATIC, listOf(cls, fields[index]), tail, mark), ExclusionSet.Empty)
        fun local(base: AccessPathBase = AccessPathBase.Argument(0), mark: MarkSlot = t) =
            Pattern(PathFact(base, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)
        fun graph(vararg calls: Pair<MethodKey, MethodKey>) = DetachedStaticCallGraph.copyOf(
            listOf(f.a, f.b, f.unknown).associate { owner -> owner.method to
                calls.filter { it.first == owner }.map { it.second.method }.toSet() }, f.cancellation)
        fun demand(completion: FrozenCompletion) = DemandStore.Builder(ap).apply {
            withCompletion(completion)
        }.build()
    }

    @Test fun `typed terminal completion follows FLOW and exact colored bridges without eager pairs`() {
        val f = Fixture()
        val completion = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, f.zero, f.c(0, f.t, Tail.EXACT))
            addBridge(f.f.a, StaticGuidanceEdge.of(f.c(0, MarkSlot.STAR), f.c(1, MarkSlot.STAR)))
            addBridge(f.f.a, StaticGuidanceEdge.of(f.c(1, f.t), f.c(2, f.u)))
            addTarget(f.f.a, f.c(2, f.u))
        }.build()
        val demand = f.demand(completion)
        assertEquals(listOf(f.c(2, f.u)), completion.local(f.f.a).targetInputs().toList())
        assertTrue(demand.explicitRows(f.f.a).isEmpty(), "The query must not store composed controls as AP rows")
        repeat(2) {
            assertEquals(setOf(existingZeroAdmission(f.ap.zero)), demand.initials(f.f.a, Reach.NORMAL, f.policy))
            assertTrue(demand.acceptsTarget(f.f.a, f.ap.zero, f.policy))
        }
        assertTrue(demand.explicitRows(f.f.a).isEmpty(), "Queries must leave the immutable seed set unchanged")
        assertFalse(demand.acceptsTarget(f.f.a, f.ap.initial(f.local()), f.policy),
            "The lazy pair has ZERO as its exit, not an arbitrary AP exit")
    }

    @Test fun `terminal composition requires the same static field and a compatible mark at each join`() {
        val f = Fixture()
        data class Case(val written: Pattern, val bridgeFrom: Pattern, val bridgeTo: Pattern,
                        val reader: Pattern, val accepted: Boolean)
        val cases = listOf(
            Case(f.c(0, f.t), f.c(0, f.t), f.c(1, f.u), f.c(1, f.u), true),
            Case(f.c(0, f.t), f.c(0, f.u), f.c(1, f.v), f.c(1, f.v), false),
            Case(f.c(0, f.t), f.c(0, f.t), f.c(1, f.u), f.c(1, f.v), false),
            Case(f.c(0, f.t), f.c(2, f.t), f.c(1, f.u), f.c(1, f.u), false),
            Case(f.c(0, f.t), f.c(0, f.t), f.c(1, f.u), f.c(3, f.u), false),
        )
        for (case in cases) {
            val completion = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
                addBoundary(f.f.a, f.zero, case.written)
                addBridge(f.f.a, StaticGuidanceEdge.of(case.bridgeFrom, case.bridgeTo))
                addTarget(f.f.a, case.reader)
            }.build()
            val demand = f.demand(completion)
            assertEquals(case.accepted, demand.acceptsTarget(f.f.a, f.ap.zero, f.policy), "$case")
            assertTrue(demand.explicitRows(f.f.a).isEmpty())
        }
    }

    @Test fun `nonzero writer keeps a paired AP exit and never authorizes a ZERO terminal`() {
        val f = Fixture()
        val x = f.local()
        val completion = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, x, f.c(0))
            addTarget(f.f.a, f.c(0))
        }.build()
        val demand = f.demand(completion)
        val input = f.f.fact(AccessPathBase.Argument(0), mark = f.t)
        assertEquals(setOf(existingZeroAdmission(f.ap.zero)), demand.initials(f.f.a, Reach.NORMAL, f.policy))
        assertEquals(listOf(input), demand.intersect(f.f.a, f.ap.zero, input, f.policy),
            "The derived (Target, x/T) pair selects its complete AP exit")
        assertFalse(demand.acceptsTarget(f.f.a, f.ap.zero, f.policy),
            "A Target entry alone must not bypass the AP exit")
        assertTrue(demand.intersect(f.f.a, f.ap.zero,
            f.f.fact(AccessPathBase.Argument(1), mark = f.t), f.policy).isEmpty())
    }

    @Test fun `static bridges cross reachable callees while terminal and writer bindings stay in their owner context`() {
        val f = Fixture()
        val other = f.f.key(f.f.a.method, "other context")
        val completion = FrozenStaticCompletion.Builder(f.ap, f.graph(f.f.a to f.f.b)).apply {
            addBoundary(f.f.a, f.zero, f.c(0))
            addBridge(f.f.b, StaticGuidanceEdge.of(f.c(0), f.c(1)))
            addTarget(f.f.a, f.c(1))
        }.build()
        val demand = f.demand(completion)
        assertTrue(demand.acceptsTarget(f.f.a, f.ap.zero, f.policy),
            "The root must see the bridge from its reachable callee")
        for (owner in listOf(f.f.b, f.f.unknown, other)) {
            assertTrue(completion.local(owner).targetInputs().none(), "$owner")
            assertTrue(demand.initials(owner, Reach.NORMAL, f.policy).isEmpty(), "$owner")
            assertFalse(demand.acceptsTarget(owner, f.ap.zero, f.policy), "$owner")
        }
        val unrelated = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, f.zero, f.c(0))
            addBridge(f.f.b, StaticGuidanceEdge.of(f.c(0), f.c(1)))
            addTarget(f.f.a, f.c(1))
        }.build()
        assertFalse(f.demand(unrelated).acceptsTarget(f.f.a, f.ap.zero, f.policy),
            "A bridge in an unrelated common method is not a composition permission")
    }

    @Test fun `terminal composition uses the run1 to run2 snapshot only`() {
        val f = Fixture()
        val completion = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, f.zero, f.c(0))
            addTarget(f.f.a, f.c(0))
        }.build()
        val demand = f.demand(completion)
        demand.validateIncoming(2)
        for (run in listOf(3, 4, 5)) assertFailsWith<IllegalStateException>("run-$run") {
            demand.validateIncoming(run)
        }
        val localOnly = DemandStore.Builder(f.ap).build()
        assertTrue(localOnly.initials(f.f.a, Reach.NORMAL, f.policy).isEmpty())
        assertFalse(localOnly.acceptsTarget(f.f.a, f.ap.zero, f.policy))
    }

    @Test fun `handoff adds a lazy ZERO to Target pair without an explicit closure publication`() {
        MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config)
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val t = MarkSlot.Concrete(f.mark("T"))
            val static = f.pattern(STATIC, path, Tail.STAR, t)
            val written = f.fact(STATIC, path, Tail.EXACT, t, layer = Layer.DEMAND)
            actor.summaries.add(f.manager.zero, written)
            actor.summaries.addDemand(f.manager.zero, written)
            actor.emitTarget(f.manager.initial(static), Target.DemandTarget)
            f.drain(actor)
            actor.freeze()
            val result = RunResult(RunStatus.COMPLETE, listOf(actor), 1, Direction.FORWARD)
            val handOff = HandOff.of(config, result, f.shared)
            val policy = handOff.demand.admissionPolicy(2, 1, Direction.BACKWARD)

            assertTrue(handOff.demand.hasStaticCompletion)
            assertEquals(2, handOff.demandEdges[f.key], "Only the two original rows are explicit")
            assertEquals(listOf(DemandPattern(written.let { f.ops.leaves(it).single() }, f.manager.zero.toPattern())),
                handOff.demand.explicitRows(f.key))
            assertEquals(setOf(existingZeroAdmission(f.manager.zero)), handOff.demand.initials(f.key, Reach.NORMAL, policy))
            assertTrue(handOff.demand.acceptsTarget(f.key, f.manager.zero, policy),
                "The composed (Target, ZERO) pair must accept both endpoints together")
            assertTrue(f.records.byEntry(f.key, f.manager.zero.toPattern()).none(),
                "Lazy demand completion must not create a retained NORMAL source summary")
        }
    }

    @Test fun `joined frozen terminal seeds remain usable after mutable run1 catalogs are released`() {
        MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val static = f.pattern(STATIC, path, Tail.STAR, MarkSlot.Concrete(f.mark("T")))
            val completed = FrozenStaticCompletion.Builder(f.manager, DetachedStaticCallGraph.EMPTY).apply {
                addBoundary(f.key, f.manager.zero.toPattern(), static)
                addTarget(f.key, static)
            }.build()
            f.shared.releaseRun1CatalogCoverage()
            val result = RunResult<RunMethodAnalyzer>(RunStatus.COMPLETE, emptyList(), 1, Direction.FORWARD,
                staticCompletion = completed)
            val handOff = HandOff.of(config, result, f.shared)
            val policy = handOff.demand.admissionPolicy(2, 1, Direction.BACKWARD)
            assertTrue(handOff.demandEdges.isEmpty(), "The joined snapshot has no explicit actor publications")
            assertEquals(setOf(existingZeroAdmission(f.manager.zero)), handOff.demand.initials(f.key, Reach.NORMAL, policy))
            assertTrue(handOff.demand.acceptsTarget(f.key, f.manager.zero, policy))
            assertTrue(handOff.demand.explicitRows(f.key).isEmpty())
        }
    }

    @Test fun `terminal lookup terminates on a colored static cycle and freezes its reader inputs`() {
        val f = Fixture()
        val builder = FrozenStaticCompletion.Builder(f.ap, f.graph()).apply {
            addBoundary(f.f.a, f.zero, f.c(0, f.t))
            addBridge(f.f.a, StaticGuidanceEdge.of(f.c(0, f.t), f.c(1, f.u)))
            addBridge(f.f.a, StaticGuidanceEdge.of(f.c(1, f.u), f.c(0, f.t)))
            addTarget(f.f.a, f.c(1, f.u))
        }
        val completion = builder.build()
        builder.addTarget(f.f.a, f.c(3, f.v))
        assertEquals(listOf(f.c(1, f.u)), completion.local(f.f.a).targetInputs().toList())
        assertTrue(f.demand(completion).acceptsTarget(f.f.a, f.ap.zero, f.policy))
    }

    @Test fun `NORMAL Target creates no backward guide and backward actors ignore it`() {
        for (run in listOf(1, 2)) MethodAnalysisFixtures().use { f ->
            val demand = if (run == 1) null else DemandStore.Builder(f.manager).build()
            val config = RunConfig(run, 1, demand, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config)
            val rule = object : CommonTaintConfigurationSink {
                override val id = "normal terminal"
                override val meta = object : CommonTaintConfigurationSinkMeta {
                    override val message = "normal terminal"
                    override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
                }
            }
            val id = f.shared.reportCatalog.intern(SinkKey(f.key.method, f.inst(0), rule.id), rule, f.key)
            actor.emitTarget(f.manager.zero, Target.NormalTarget(id))
            f.drain(actor)
            actor.freeze()
            assertEquals(if (run == 1) 1 else 0, actor.targets.size)
            assertTrue(actor.outgoingTargets.isEmpty())
            val result = RunResult(RunStatus.COMPLETE, listOf(actor), run, config.direction)
            val handOff = HandOff.of(config, result, f.shared)
            assertTrue(handOff.demandEdges.isEmpty())
            val next = handOff.demand.admissionPolicy(run + 1, run, config.direction.let {
                if (it == Direction.FORWARD) Direction.BACKWARD else Direction.FORWARD
            })
            assertTrue(handOff.demand.initials(f.key, Reach.NORMAL, next).isEmpty())
            assertFalse(handOff.demand.acceptsTarget(f.key, f.manager.zero, next))
        }
    }
}
