package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

class LoopBlockDeepNoLeaveTest {
    @Test fun `exceptional ZERO normal demand keeps a four field source through the fifth run`() {
        DriverFixtures().use { f ->
            val p = f.program
            // while(true) { sourceAtFFFF(x); x=x.f; sinkRootT(x); }
            val b = p.method("deep-loop-no-leave", listOf(listOf(1), listOf(2), listOf(3),
                listOf(4), listOf(5), listOf(2), emptyList(), emptyList()),
                normalExit = 6, exceptionalExit = 7, backwardExitDiscovery = true).key()
            val arg = AccessPathBase.Argument(0)
            val x = AccessPathBase.LocalVar(0)
            val field = p.field("f")
            val t = MarkSlot.Concrete(p.mark("T"))
            p.statement(b, 1, MicroEdgeBuilder().apply { move(x, arg) }.build())
            val source = PathEdge(ZERO_FACT, PathFact(x, List(4) { field }, Tail.EXACT, t), ExclusionSet.Empty)
            fun plan(sourceCall: Boolean, sinks: List<SinkRule> = emptyList()) = CallPlan(setOf(x), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(keepEdge(x), ZERO_KEEP)),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, if (sourceCall) SOURCES else UNRESOLVED,
                    if (sourceCall) f.summary(keepEdge(x), ZERO_KEEP, source) else f.summary(keepEdge(x), ZERO_KEEP)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(keepEdge(x), ZERO_KEEP))
            ), sinks, BEFORE, AFTER)
            p.call(b, 3, plan(sourceCall = true))
            p.statement(b, 4, MicroEdgeBuilder().apply { read(x, x, listOf(field)) }.build())
            val sink = SinkRule(f.rule("deep-loop-root-sink"), 0, listOf(p.pattern(x, mark = t)), emptyList())
            p.call(b, 5, plan(sourceCall = false, sinks = listOf(sink)))
            val result = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4, 5, 6)), 15.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(b))
            for (run in listOf(3, 5)) assertTrue(f.configs.single { it.index == run }.seeds
                .allowsSource(b, p.inst(b, 3), source), "run-$run keeps the same physical source permission")
            val third = f.results.single { it.runIndex == 3 }.analyzers.single { it.key == b }
            assertTrue(third.outgoingTargets.any { it.premise.isZero && it.target == Target.DemandTarget })
            assertFalse(third.targets.any { it.premise.isZero && it.target is Target.NormalTarget })
            assertEquals(5, result.end.run)
            assertEquals(1, result.entries.size)
            assertTrue(result.entries.any { it.descriptor.key.ruleId == "deep-loop-root-sink" })
            assertTrue(f.processed.none { it.run % 2 == 1 && it.delta.node.location.index in listOf(6, 7) })
        }
    }
}
