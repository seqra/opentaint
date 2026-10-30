package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*

class FieldLimitScheduleTest {
    @Test fun `run2 static validator accepts the selected bounded depth without broadening anchors`() {
        val f = EngineShellFixtures()
        val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
        val path = listOf(cls, f.field("f"), f.field("g"))
        for (tail in listOf(Tail.EXACT, Tail.ANY, Tail.STAR)) {
            val actual = f.pattern(STATIC, path, tail)
            assertFailsWith<IllegalStateException> { validateRun2StaticFullInput(f.manager, actual) }
            assertTrue(validateRun2StaticFullInput(f.manager, actual, fieldLimit = 2))
            val tooDeep = actual.copy(fact = actual.fact.copy(path = path + f.field("h")))
            assertFailsWith<IllegalStateException> { validateRun2StaticFullInput(f.manager, tooDeep, 2) }
        }
        for (tail in listOf(Tail.ANY, Tail.STAR)) {
            assertFailsWith<IllegalStateException> {
                validateRun2StaticFullInput(f.manager, f.pattern(STATIC, listOf(cls), tail), 2)
            }
        }
        assertFailsWith<IllegalStateException> {
            validateRun2StaticFullInput(f.manager, f.pattern(STATIC, path, Tail.ANY_TAINT), 2)
        }
        for (limit in listOf(1, 2)) assertFailsWith<IllegalStateException> {
            validateRun2StaticFullInput(f.manager, f.pattern(STATIC, path.take(2) + cls), limit)
        }
    }

    @Test fun `default selection keeps the repeated first limit and unknown values fail`() {
        assertSame(IncreasingLimits, configuredIncreasingLimits(null))
        assertSame(IncreasingLimits, configuredIncreasingLimits("REPEAT_RUN1"))
        assertSame(RunIndexLimits, configuredIncreasingLimits("RUN_INDEX"))
        assertEquals(listOf(1, 1, 2, 3, 4, 5), (1..6).map(IncreasingLimits::fieldLimit))
        assertEquals((1..6).toList(), (1..6).map(RunIndexLimits::fieldLimit))
        assertFailsWith<IllegalStateException> { configuredIncreasingLimits("RUN_INDEx") }
        for (schedule in FieldLimitSchedule.entries) {
            assertFailsWith<IllegalArgumentException> { schedule.fieldLimit(0) }
            assertFailsWith<IllegalArgumentException> { schedule.fieldLimit(-1) }
        }
    }

    @Test fun `an explicit schedule validates each config without relaxing default validation`() {
        val f = EngineShellFixtures()
        val demand = DemandStore.Builder(f.manager).build()
        for (schedule in FieldLimitSchedule.entries) for (index in 1..8) {
            val expected = schedule.fieldLimit(index)
            val config = RunConfig(index, expected, if (index == 1) null else demand,
                f.records, SeedIndex.EMPTY, emptyList(), fieldLimitSchedule = schedule)
            assertEquals(expected, config.mode.fieldLimit)
            assertEquals(index > 1, config.restricted)
            assertEquals(index % 2 == 1, config.direction == org.opentaint.dataflow.bidi.ap.Direction.FORWARD)
            assertEquals(index > 1 && index % 2 == 1, config.seededSources)
            assertSame(schedule, config.fieldLimitSchedule)
            for (wrong in setOf(0, expected - 1, expected + 1)) {
                assertFailsWith<IllegalArgumentException> {
                    RunConfig(index, wrong, if (index == 1) null else demand,
                        f.records, SeedIndex.EMPTY, emptyList(), fieldLimitSchedule = schedule)
                }
            }
        }
        assertFailsWith<IllegalArgumentException> {
            RunConfig(2, 2, demand, f.records, SeedIndex.EMPTY, emptyList())
        }
    }

    @Test fun `actual driver keeps selected schedule across barriers and later demand remains local`() {
        val property = "opentaint.bidi.fieldLimitSchedule"
        val old = System.getProperty(property)
        try {
            System.setProperty(property, "RUN_INDEX")
            val selected = configuredIncreasingLimits()
            val policy = object : IterationPolicy by selected {
                override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>,
                                           frontiers: List<Frontier>): Boolean = run.index < 3
            }
            DriverFixtures().use { f ->
                val program = f.persistentDemand()
                val driver = f.driver(policy)
                System.setProperty(property, "REPEAT_RUN1")
                val report = driver.analyze(listOf(program.root))
                assertEquals(listOf(1, 2, 3), f.configs.map { it.fieldLimit })
                assertTrue(f.configs.all { it.fieldLimitSchedule == FieldLimitSchedule.RUN_INDEX })
                assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
                assertEquals(listOf(1, 2, 3), driver.frontiers.map { it.run })
                assertFalse(f.configs[2].demand!!.hasStaticCompletion)
                assertEquals(3, report.end.run)
                assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
                assertTrue(driver.frontiers.last().demandEdges.isEmpty())
            }
        } finally {
            if (old == null) System.clearProperty(property) else System.setProperty(property, old)
        }
    }
}
