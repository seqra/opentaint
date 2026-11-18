package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

/** Native components shared by production and the selected proposal. NE itself
 * is not installed: the cut test checks its current MAY predecessor's location,
 * DEMAND layer and protection; Lean checks the proposed NE replacement. */
class ProtectedCleanerGrowthComponentsTest {
    @Test fun `root cleaner preserves nonempty MUST and STAR inputs with survivor protection`() {
        val f = StoreFixtures()
        val p = AccessPathBase.Argument(0)
        val field = f.field("f")
        val t = f.mark("T")
        val mark = MarkSlot.Concrete(t)
        for (depth in listOf(1, 2, 5)) for (tail in listOf(Tail.ANY_TAINT, Tail.STAR)) {
            val layer = if (tail == Tail.STAR) Layer.DEMAND else Layer.NORMAL
            val value = f.fact(p, List(depth) { field }, tail, mark, layer = layer)
            val initial = f.manager.initial(f.ops.leaves(value).single())
            val out = CollectingOut()
            f.ops.clean(value, initial, Cleaner(p, null, CleanReach.EXACT, t),
                ApMode(false, Direction.FORWARD, depth + 1), out)
            val result = out.results.single() as TaintTree
            assertEquals(layer, result.layer)
            assertEquals(f.ops.leaves(value).toList(), f.ops.leaves(result).toList())
            assertNotNull(result.nonSubsumable)
        }
    }

    @Test fun `run3 body has a NORMAL concrete reader and a protected DEMAND cut under the same initial`() {
        MethodAnalysisFixtures(listOf(listOf(1), listOf(2, 3), listOf(5), listOf(4), listOf(5), emptyList()), 5).use { f ->
            val p = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val tmp = AccessPathBase.LocalVar(10)
            val field = f.field("f")
            val t = f.mark("T")
            val mark = MarkSlot.Concrete(t)
            val keep = StatementSummary(setOf(p), listOf(MicroEdge.of(keepEdge(p))), emptyList(), emptyMap())
            f.call(0, CallPlan(setOf(p), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, listOf(CleanStep.Clean(Cleaner(p, null, CleanReach.EXACT, t)))),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), emptyList(), BEFORE, AFTER))
            f.statement(2, MicroEdgeBuilder().apply { read(ret, p, listOf(field, field)) }.build())
            f.statement(3, MicroEdgeBuilder().apply {
                write(tmp, listOf(field), false, listOf(p), emptyList())
            }.build())
            f.statement(4, MicroEdgeBuilder().apply {
                write(ret, listOf(field), false, listOf(tmp), emptyList())
            }.build())
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(f.pattern(p, listOf(field), Tail.ANY, mark),
                    f.pattern(ret, listOf(field), Tail.STAR, mark)))
            }.build()
            val actor = f.core(index = 3, L = 2, demand = demand,
                callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            f.submitRestricted(actor, f.fact(p, emptyList(), Tail.ANY_TAINT, mark))
            f.drain(actor)
            val initial = f.pattern(p, listOf(field), Tail.ANY_TAINT, mark)
            val rows = actor.summaries.all().filter { (premise, _) ->
                (premise as? InitialAp)?.toPattern() == initial
            }.flatMap { (_, value) -> f.ops.leaves(value).map { Triple(it, value.layer,
                (value as? TaintTree)?.nonSubsumable != null) } }.toSet()
            assertContains(rows, Triple(f.pattern(ret, listOf(field), Tail.ANY_TAINT, mark), Layer.NORMAL, true))
            assertContains(rows, Triple(f.pattern(ret, listOf(field, field), Tail.ANY, mark), Layer.DEMAND, true))
            println("PROTECTED_GROWTH_RUN3 $rows")
        }
    }

    @Test fun `NORMAL and DEMAND sink targets coexist in either arrival order`() {
        val f = StoreFixtures()
        val normal = TargetSummary(f.manager.zero, Target.NormalTarget(ReportId(1)))
        val demand = TargetSummary(f.manager.zero, Target.DemandTarget)
        for (rows in listOf(listOf(normal, demand), listOf(demand, normal))) {
            val index = PublicationIndex(f.manager, f.ops)
            rows.forEach { index.addTargets(listOf(it)) }
            val part = Subscription(f.method, CallerRef(f.method, f.manager.zero, Layer.NORMAL, f.inst(1)),
                Layer.NORMAL, f.ops.startFact(f.manager.zero, ApMode(false, Direction.FORWARD, 2)))
            assertEquals(setOf(normal, demand), index.targetCandidates(part, ApMode(false, Direction.FORWARD, 2))
                .map { it.first }.toSet())
        }
    }
}
