package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.Direction
import org.opentaint.dataflow.bidi.ap.MarkMode
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.settledNormalSink
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class HardRunLimitPolicyTest {
    private fun config(f: DriverFixtures, index: Int, schedule: FieldLimitSchedule = FieldLimitSchedule.REPEAT_RUN1) =
        RunConfig(index, schedule.fieldLimit(index),
            if (index == 1) null else DemandStore.Builder(f.manager).build(),
            f.records, SeedIndex.EMPTY, emptyList(), run1MarkMode = MarkMode.FULL,
            fieldLimitSchedule = schedule)

    @Test
    fun `default production policies cap eleven without changing either field schedule`() {
        for ((name, schedule) in listOf(null to FieldLimitSchedule.REPEAT_RUN1,
            "REPEAT_RUN1" to FieldLimitSchedule.REPEAT_RUN1, "RUN_INDEX" to FieldLimitSchedule.RUN_INDEX)) {
            val policy = assertIs<HardRunLimitPolicy>(configuredIncreasingLimits(name))
            assertEquals(11, policy.lastForwardRun)
            assertEquals(schedule, policy.fieldLimitSchedule)
            assertEquals((1..11).map(schedule::fieldLimit), (1..11).map(policy::fieldLimit))
        }
        assertFailsWith<IllegalStateException> { configuredIncreasingLimits("invalid") }
    }

    @Test
    fun `cap preserves delegate timeout and earlier stop reason`() {
        DriverFixtures().use { f ->
            var observedTimeout: Duration? = null
            val delegate = object : IterationPolicy by IncreasingLimits {
                override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>) = false
                override fun stopReason(run: RunConfig) = EndReason.STOP_RULE
                override fun timeout(run: RunConfig, remaining: Duration): Duration {
                    observedTimeout = remaining
                    return 2.seconds
                }
            }
            val policy = HardRunLimitPolicy(delegate, 11)
            val earlier = config(f, 9)
            val result = RunResult<RunMethodAnalyzer>(RunStatus.COMPLETE, emptyList(), 9, Direction.FORWARD)
            assertFalse(policy.continueAfter(earlier, result, emptyList()))
            assertEquals(EndReason.STOP_RULE, policy.stopReason(earlier))
            assertEquals(2.seconds, policy.timeout(earlier, 7.seconds))
            assertEquals(7.seconds, observedTimeout)
            val final = config(f, 11)
            val finalResult = RunResult<RunMethodAnalyzer>(RunStatus.COMPLETE, emptyList(), 11, Direction.FORWARD)
            assertFalse(policy.continueAfter(final, finalResult, emptyList()))
            assertEquals(EndReason.RUN_LIMIT, policy.stopReason(final))
        }
        for (invalid in listOf(-1, 0, 2, 10, 12)) {
            assertFailsWith<IllegalArgumentException> { HardRunLimitPolicy(IncreasingLimits, invalid) }
        }
    }

    @Test
    fun `persistent native demand stops after completed forward eleven and never starts twelve`() {
        DriverFixtures().use { f ->
            val case = f.persistentDemand()
            val driver = f.driver(configuredIncreasingLimits(null), budget = 15.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(case.root))
            assertEquals((1..11).toList(), f.configs.map { it.index })
            assertEquals((1..11).map { maxOf(1, it - 1) }, f.configs.map { it.fieldLimit })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals((1..11).toList(), driver.frontiers.map { it.run })
            assertTrue(driver.frontiers.last().demandEdges.isNotEmpty(), "RUN_LIMIT must not claim empty-demand convergence")
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 11, Direction.FORWARD, EndReason.RUN_LIMIT), report.end)
        }
    }

    @Test
    fun `empty demand wins over the cap at its completed forward barrier`() {
        DriverFixtures().use { f ->
            val case = f.settledNormalSink()
            val driver = f.driver(HardRunLimitPolicy(IncreasingLimits, 1), run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(case.root))
            assertEquals(listOf(1), f.configs.map { it.index })
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 1, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(case.rule, report.entries.single().descriptor.rule)
        }
    }

    @Test
    fun `explicit finite native policy still stops earlier with POLICY`() {
        DriverFixtures().use { f ->
            val case = f.persistentDemand()
            val policy = HardRunLimitPolicy(FixedLimits(listOf(1, 1, 2)), 11)
            val driver = f.driver(policy, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(case.root))
            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.POLICY), report.end)
        }
    }

    @Test
    fun `incomplete eleventh engine keeps earlier confirmed reports and its timeout`() {
        DriverFixtures().use { f ->
            val demand = f.persistentDemand()
            val confirmed = f.settledNormalSink()
            val driver = f.driver(configuredIncreasingLimits(null), budget = 15.seconds,
                run1MarkMode = MarkMode.FULL, invokeRun = { run, owner, timeout ->
                    f.run(run, owner, if (run.index == 11) Duration.ZERO else timeout)
                })
            val report = driver.analyze(listOf(demand.root, confirmed.root))
            assertEquals((1..11).toList(), f.configs.map { it.index })
            assertEquals(RunStatus.TIMEOUT, f.results.last().status)
            assertEquals((1..10).toList(), driver.frontiers.map { it.run })
            assertEquals(AnalysisEnd(RunStatus.TIMEOUT, 11, Direction.FORWARD, EndReason.ABNORMAL), report.end)
            assertEquals(confirmed.rule, report.entries.single().descriptor.rule)
        }
    }

    @Test
    fun `failed final barrier is abnormal and does not commit the eleventh frontier`() {
        DriverFixtures().use { f ->
            val case = f.persistentDemand()
            var barriers = 0
            val driver = f.driver(configuredIncreasingLimits(null), budget = 15.seconds,
                run1MarkMode = MarkMode.FULL, guardBarrier = { _, body ->
                    if (++barriers == 11) throw IllegalStateException("selected final barrier failure")
                    body()
                })
            val report = driver.analyze(listOf(case.root))
            assertEquals((1..11).toList(), f.configs.map { it.index })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            assertEquals((1..10).toList(), driver.frontiers.map { it.run })
            assertEquals(AnalysisEnd(RunStatus.FAILED, 11, Direction.FORWARD, EndReason.ABNORMAL), report.end)
        }
    }
}
