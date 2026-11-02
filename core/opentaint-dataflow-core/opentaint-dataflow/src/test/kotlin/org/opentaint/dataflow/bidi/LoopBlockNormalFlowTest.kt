package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.seconds

class LoopBlockNormalFlowTest {
    @Test fun `normal source passes local loop summaries to a later sink in run one`() {
        DriverFixtures().use { f ->
            val p = f.program
            // source(x); while(again()) { x=x; } sink(x);
            val method = p.method("loop-normal-source-sink", listOf(
                listOf(1), listOf(2), listOf(3, 4), listOf(2), listOf(5), emptyList(), emptyList()),
                normalExit = 5, exceptionalExit = 6).key()
            val x = AccessPathBase.LocalVar(0)
            val mark = MarkSlot.Concrete(p.mark("T"))
            val source = PathEdge(ZERO_FACT, PathFact(x, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)
            fun plan(sourceStep: Boolean, sinks: List<SinkRule> = emptyList()) = CallPlan(setOf(x), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(keepEdge(x), ZERO_KEEP)),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, if (sourceStep) SOURCES else UNRESOLVED,
                    if (sourceStep) f.summary(keepEdge(x), ZERO_KEEP, source) else f.summary(keepEdge(x), ZERO_KEEP)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(keepEdge(x), ZERO_KEEP))
            ), sinks, BEFORE, AFTER)
            p.call(method, 1, plan(sourceStep = true))
            p.statement(method, 3, MicroEdgeBuilder().apply { move(x, x) }.build())
            val sink = SinkRule(f.rule("loop-normal-sink"), 0, listOf(p.pattern(x, mark = mark)), emptyList())
            p.call(method, 4, plan(sourceStep = false, sinks = listOf(sink)))
            val result = f.driver(FixedLimits(listOf(1, 1, 2)), 10.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(method))
            assertEquals(1, result.end.run)
            assertEquals(1, result.entries.size)
            assertTrue(result.entries.any { it.descriptor.key.ruleId == "loop-normal-sink" })
            assertTrue(f.results.single().analyzers.single().blockSummaries().any())
        }
    }
}
