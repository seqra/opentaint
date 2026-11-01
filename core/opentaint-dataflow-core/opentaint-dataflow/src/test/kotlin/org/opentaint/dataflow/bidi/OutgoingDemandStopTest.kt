package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.ExitRules
import org.opentaint.dataflow.bidi.interp.RuleStatement
import org.opentaint.dataflow.bidi.interp.SinkRule
import org.opentaint.dataflow.bidi.interp.StatementSummary
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Controlled joined actor results exercise the production barrier and its ordering.
 * The fixtures prescribe selected rows independently from observed input work.
 */
class OutgoingDemandStopTest {
    private val argument = AccessPathBase.Argument(0)
    private val returned = AccessPathBase.Return

    private class StopCase : AutoCloseable {
        val f = MethodAnalysisFixtures()
        val key = f.key
        val mark = MarkSlot.Concrete(f.mark("T"))
        val input = f.pattern(AccessPathBase.Argument(0), mark = mark)
        val rule = object : CommonTaintConfigurationSink {
            override val id = "unconfirmed stop candidate"
            override val meta = object : CommonTaintConfigurationSinkMeta {
                override val message = id
                override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
            }
        }
        val configs = ArrayList<RunConfig>()
        val results = ArrayList<RunResult<RunMethodAnalyzer>>()
        val policyCalls = ArrayList<Int>()
        val flowInitial = f.manager.initial(f.pattern(AccessPathBase.Argument(0), tail = Tail.STAR,
            mark = MarkSlot.STAR))
        val flowResult = f.fact(AccessPathBase.Return, tail = Tail.STAR, mark = MarkSlot.STAR)

        init {
            val sink = SinkRule(rule, 0, listOf(input), emptyList())
            f.exitRules(2, ExitRules(RuleStatement(StatementSummary.EMPTY,
                StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
        }

        fun driver(
            prescribe: (RunConfig, RunMethodAnalyzer) -> Unit = { _, _ -> },
            failed: RunStatus? = null,
            reportAtRun3: Boolean = true,
            guard: (SharedObjects, () -> Next) -> Next = { _, body -> body() },
        ): IterationDriver = IterationDriver(object : IterationPolicy {
            override fun fieldLimit(runIndex: Int): Int = IncreasingLimits.fieldLimit(runIndex)
            override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>,
                                       frontiers: List<Frontier>): Boolean {
                policyCalls += run.index
                return run.index < 3
            }
        }, f.shared, 5.seconds, { config, _, _ ->
            configs += config
            if (config.index == 3 && failed != null) {
                RunResult<RunMethodAnalyzer>(failed, emptyList(), config.index, config.direction)
            } else {
                val actor = f.core(config)
                // A raw NORMAL relation must be persisted before the stop decision.
                actor.summaries.addAdmitted(flowInitial, flowResult)
                if (config.direction == Direction.FORWARD) {
                    // Run-1 has independent refinement work and a settled report.
                    if (config.index == 1) actor.emitTarget(f.manager.zero, Target.DemandTarget)
                    if (config.index == 1 || reportAtRun3) {
                        val id = f.shared.reportCatalog.intern(SinkKey(key.method, f.inst(2), rule.id), rule, key)
                        actor.emitTarget(f.manager.zero, Target.NormalTarget(id))
                    }
                    // Seed capture is independent of whether terminal C5 publishes a row.
                    actor.sinkSeeds += Seed.Sink(rule, key, f.inst(2), input)
                }
                prescribe(config, actor)
                f.drain(actor)
                actor.freeze()
                RunResult(RunStatus.COMPLETE, listOf(actor), config.index, config.direction)
            }.also(results::add)
        }, guard)

        override fun close() = f.close()
    }

    @Test
    fun `empty selected output stops despite demand input work and retains complete barrier products`() {
        StopCase().use { c ->
            val driver = c.driver(prescribe = { config, actor ->
                if (config.index == 3) {
                    // Input-only presence is no longer counted by the callee.
                    // Simulate completed DEMAND work, with no selected output.
                    actor.emitAfter(c.f.manager.zero, c.f.inst(1),
                        c.f.fact(argument, mark = c.mark, layer = Layer.DEMAND))
                }
            })
            val report = driver.analyze(listOf(c.key))

            assertEquals(listOf(1, 2, 3), c.configs.map { it.index })
            assertEquals(listOf(1), c.policyCalls,
                "Run-1 can carry virtual static demand; backward runs do not ask the policy")
            assertTrue(c.results.last().demandLayerEdges > 0L)
            assertTrue(driver.frontiers.last().demandEdges.isEmpty())
            assertTrue(driver.frontiers.last().seeds > 0,
                "A sink seed does not override the empty outgoing-demand stop")
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD,
                EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
            assertEquals(listOf(1, 2, 3), driver.frontiers.map { it.run })
            assertTrue(c.f.records.byEntry(c.key, c.flowInitial.toPattern()).any { record ->
                record.direction == Direction.FORWARD && record.conclusion == c.flowResult
            })
        }
    }

    @Test
    fun `a skipped later normal observation retains its earlier report and stops on empty demand`() {
        StopCase().use { c ->
            val driver = c.driver(reportAtRun3 = false)
            val report = driver.analyze(listOf(c.key))
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
            assertTrue(driver.frontiers.last().demandEdges.isEmpty())
            assertEquals(listOf(1), c.policyCalls)
            assertEquals(listOf(1, 2, 3), driver.frontiers.map { it.run })
        }
    }

    @Test
    fun `normal ND selected support prevents the new stop when no demand object was observed`() {
        StopCase().use { c ->
            val driver = c.driver(prescribe = { config, actor ->
                if (config.index == 3) {
                    val first = c.f.manager.initial(c.input)
                    val second = c.f.manager.initial(c.f.pattern(AccessPathBase.Argument(1), mark = c.mark))
                    val joint = c.f.manager.premiseOf(listOf(first, second))
                    val target = c.f.fact(returned, mark = c.mark)
                    actor.summaries.addAdmitted(joint, target)
                }
            })
            val report = driver.analyze(listOf(c.key))

            assertEquals(0L, c.results.last().demandLayerEdges)
            assertEquals(mapOf(c.key to 2), driver.frontiers.last().demandEdges,
                "Each full ND member contributes selected NORMAL support")
            assertEquals(listOf(1, 3), c.policyCalls)
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD,
                EndReason.POLICY), report.end)
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
        }
    }

    @Test
    fun `incomplete restricted runs do not use the empty outgoing-demand stop`() {
        for (status in listOf(RunStatus.TIMEOUT, RunStatus.OOM, RunStatus.FAILED)) StopCase().use { c ->
            val driver = c.driver(failed = status)
            val report = driver.analyze(listOf(c.key))
            assertEquals(AnalysisEnd(status, 3, Direction.FORWARD, EndReason.ABNORMAL), report.end)
            assertEquals(listOf(1, 2), driver.frontiers.map { it.run })
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
            assertEquals(listOf(1), c.policyCalls)
        }
    }

    @Test
    fun `late memory cancellation overrides the completed empty outgoing-demand decision`() {
        StopCase().use { c ->
            var barrier = 0
            val driver = c.driver(guard = { shared, body ->
                val next = body()
                if (++barrier == 3) shared.cancellation.cancel()
                next
            })
            val report = driver.analyze(listOf(c.key))
            assertEquals(AnalysisEnd(RunStatus.OOM, 3, Direction.FORWARD, EndReason.ABNORMAL), report.end)
            assertEquals(listOf(1, 2, 3), driver.frontiers.map { it.run })
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
        }
    }

    @Test
    fun `a barrier checkpoint cancellation remains OOM and preserves the earlier report`() {
        StopCase().use { c ->
            var barrier = 0
            val driver = c.driver(guard = { shared, body ->
                if (++barrier == 3) {
                    shared.cancellation.cancel()
                    shared.cancellation.checkpoint()
                }
                body()
            })
            val report = driver.analyze(listOf(c.key))
            assertEquals(AnalysisEnd(RunStatus.OOM, 3, Direction.FORWARD, EndReason.ABNORMAL), report.end)
            assertEquals(listOf(1, 2), driver.frontiers.map { it.run })
            assertEquals(c.rule.id, report.entries.single().descriptor.key.ruleId)
            assertFalse(c.f.cancellation.isActive())
            assertFailsWith<Cancellation.Cancelled> { c.f.cancellation.checkpoint() }
        }
    }
}
