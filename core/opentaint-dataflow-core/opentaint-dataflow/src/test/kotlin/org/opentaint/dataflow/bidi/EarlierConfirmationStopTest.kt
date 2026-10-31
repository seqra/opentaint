package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.settledNormalSink
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** A settled report survives later skipped ZERO paths without forcing another run. */
class EarlierConfirmationStopTest {
    @Test fun `settled NormalTarget survives an independent DemandTarget refinement and does not become guidance`() {
        DriverFixtures().use { f ->
            val settled = f.settledNormalSink()
            val pending = f.persistentDemand()
            val callbacks = ArrayList<Int>()
            val driver = f.driver(object : IterationPolicy {
                override fun fieldLimit(runIndex: Int) = maxOf(1, runIndex - 1)
                override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>,
                                           frontiers: List<Frontier>): Boolean {
                    callbacks += run.index
                    assertTrue(frontiers.last().targetDemand > 0)
                    assertEquals(1, frontiers.last().reportedSinks)
                    return run.index < 3
                }
            }, budget = 10.seconds)
            val report = driver.analyze(listOf(settled.root, pending.root))
            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertEquals(listOf(1, 3), callbacks)
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.POLICY), report.end)
            val entry = report.entries.single()
            assertSame(settled.rule, entry.descriptor.rule)
            assertEquals(settled.sink, entry.descriptor.key.statement)
            assertTrue(f.configs[1].normalTargets.contains(settled.root, f.manager.zero, entry.id))
            assertTrue(f.configs[2].normalTargets.contains(settled.root, f.manager.zero, entry.id))
            assertTrue(f.configs[1].seeds.at(settled.root, settled.sink).isEmpty())
            assertTrue(f.configs[1].seeds.at(pending.root, pending.sink).isNotEmpty())
            assertTrue(driver.frontiers.last().demandEdges.isNotEmpty(), "Only the independent DEMAND path requires continuation")
            assertEquals(1, driver.frontiers.last().reportedSinks)
            assertTrue(f.results.drop(1).flatMap { it.analyzers }.flatMap { it.targets }
                .none { it.target == Target.NormalTarget(entry.id) }, "Settled ZERO terminal is not replayed")
        }
    }
}
