package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

class TargetCallTest {
    private fun core(f: MethodAnalysisFixtures, run: Int = 3): RunMethodAnalyzer {
        val config = RunConfig(run, maxOf(1, run - 1),
            if (run == 1) null else DemandStore.Builder(f.manager).build(), f.records,
            SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
        return f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
    }

    @Test fun `normal terminal accepts only complete normal support and never enters return suffix`() {
        for (caller in Layer.entries) for (link in Layer.entries) MethodAnalysisFixtures().use { f ->
            val actor = core(f)
            val p = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
            val original = f.manager.initial(f.pattern(AccessPathBase.Argument(1)))
            val row = TargetSummary(p, Target.NormalTarget(ReportId(7)))
            val part = Subscription(f.store.key("callee"), CallerRef(actor.key, original, caller, f.inst(1)),
                link, f.fact(AccessPathBase.Argument(0), layer = link))
            actor.applyTarget(part, row, 0)
            val expected = if (caller == Layer.NORMAL && link == Layer.NORMAL)
                setOf(TargetSummary(original, row.target)) else emptySet()
            assertEquals(expected, actor.targets)
            assertTrue(actor.summaries.all().none(), "Target never binds a return or touches CFG delivery")
            assertTrue(f.processed.isEmpty())
        }
    }

    @Test fun `normal terminal is ignored backward and demand terminal does not turn into normal`() {
        MethodAnalysisFixtures().use { f ->
            val actor = core(f, run = 2)
            val p = f.manager.initial(f.pattern())
            val part = Subscription(f.store.key("callee"), CallerRef(actor.key, p, Layer.NORMAL, f.inst(1)),
                Layer.NORMAL, f.fact())
            actor.applyTarget(part, TargetSummary(p, Target.NormalTarget(ReportId(1))), 0)
            assertTrue(actor.targets.isEmpty())
            actor.applyTarget(part, TargetSummary(p, Target.DemandTarget), 0)
            assertEquals(setOf(TargetSummary(p, Target.DemandTarget)), actor.targets)
            assertTrue(actor.outgoingTargets.isEmpty(), "Paired C5 still requires selected demand")
        }
    }

    @Test fun `ND terminal waits for all members at the same call and preserves full original union`() = MethodAnalysisFixtures().use { f ->
        val actor = core(f)
        val a = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
        val b = f.manager.initial(f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U"))))
        val premise = f.manager.union(a, b)
        val x = f.manager.initial(f.pattern(AccessPathBase.Argument(2)))
        val y = f.manager.initial(f.pattern(AccessPathBase.Argument(3), mark = MarkSlot.Concrete(f.mark("U"))))
        val row = TargetSummary(premise, Target.NormalTarget(ReportId(3)))
        val callee = f.store.key("callee")
        fun part(origin: InitialAp, value: InitialAp, call: Int, layer: Layer = Layer.NORMAL) =
            Subscription(callee, CallerRef(actor.key, origin, Layer.NORMAL, f.inst(call)), layer,
                f.ops.startFact(value).let { if (it is TaintTree) it.withLayer(layer) else it })
        actor.applyTarget(part(x, a, 1), row, 0)
        actor.applyTarget(part(y, b, 2), row, 1)
        assertTrue(actor.targets.isEmpty(), "Slots from different statements cannot join")
        actor.applyTarget(part(y, b, 1, Layer.DEMAND), row, 1)
        assertTrue(actor.targets.isEmpty(), "A DEMAND member cannot complete a NORMAL terminal")
        actor.applyTarget(part(y, b, 1), row, 1)
        val expected = TargetSummary(f.manager.union(x, y), row.target)
        assertEquals(setOf(expected), actor.targets)
        repeat(3) { actor.applyTarget(part(y, b, 1), row, 1) }
        assertEquals(setOf(expected), actor.targets)
    }

    @Test fun `saved normal terminal applies before an empty current demand gate`() = MethodAnalysisFixtures().use { f ->
        val callee = f.store.key("callee")
        val initial = f.manager.initial(f.pattern())
        val saved = NormalTargetStore(f.manager, sequenceOf(OwnedNormalTarget(callee, initial, ReportId(8))))
        val config = RunConfig(3, 2, DemandStore.Builder(f.manager).build(), f.records, SeedIndex.EMPTY,
            listOf(f.key), normalTargets = saved)
        f.call(1, CallPlan(setOf(AccessPathBase.Argument(0)), listOf(
            CallStage.Callees(CallPoint.BEFORE, CallPoint.AFTER, listOf(callee))),
            emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
        val actor = f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
        actor.emitAfter(f.manager.zero, f.inst(0), f.fact())
        f.drain(actor)
        assertEquals(setOf(TargetSummary(f.manager.zero, Target.NormalTarget(ReportId(8)))), actor.targets)
        assertTrue(f.subscriptions.isEmpty())
        assertTrue(f.sentInitials.isEmpty())
        assertTrue(f.sentLinks.isEmpty())
    }

    @Test fun `concrete MUST applicable-only child cannot produce a normal terminal`() = MethodAnalysisFixtures().use { f ->
        val actor = core(f)
        val p = f.manager.initial(f.pattern(tail = Tail.ANY_TAINT))
        val original = f.manager.initial(f.pattern(AccessPathBase.Argument(1)))
        val part = Subscription(f.store.key("callee"), CallerRef(actor.key, original, Layer.NORMAL, f.inst(1)),
            Layer.NORMAL, f.fact(path = listOf(f.field("child")), tail = Tail.ANY_TAINT))
        actor.applyTarget(part, TargetSummary(p, Target.NormalTarget(ReportId(9))), 0)
        assertTrue(actor.targets.isEmpty())
        actor.applyTarget(part, TargetSummary(p, Target.DemandTarget), 0)
        assertTrue(actor.targets.isEmpty(), "Existing inside selection rejects the child for either terminal kind")
    }

    @Test fun `abstract MUST terminal needs definite uniform input`() = MethodAnalysisFixtures().use { f ->
        val actor = core(f)
        val p = f.manager.initial(f.pattern(tail = Tail.ANY_TAINT, mark = MarkSlot.STAR))
        val origin = f.manager.initial(f.pattern())
        val row = TargetSummary(p, Target.NormalTarget(ReportId(1)))
        for (tail in listOf(Tail.STAR, Tail.ANY)) {
            val input = f.fact(tail = tail, mark = MarkSlot.STAR)
            val part = Subscription(f.store.key("callee"), CallerRef(actor.key, origin, Layer.NORMAL, f.inst(1)),
                Layer.NORMAL, input)
            actor.applyTarget(part, row, 0)
            assertTrue(actor.targets.isEmpty())
        }
        val input = f.fact(tail = Tail.ANY_TAINT, mark = MarkSlot.STAR)
        actor.applyTarget(Subscription(f.store.key("callee"), CallerRef(actor.key, origin, Layer.NORMAL, f.inst(1)),
            Layer.NORMAL, input), row, 0)
        assertEquals(setOf(TargetSummary(origin, row.target)), actor.targets)
    }
}
