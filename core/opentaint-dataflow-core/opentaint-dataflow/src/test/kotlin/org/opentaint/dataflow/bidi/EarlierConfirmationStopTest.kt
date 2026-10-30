package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Analyzer inventory 9: explicit joined-result witness-boundary regression, not a native-program theorem. */
class EarlierConfirmationStopTest {
    /** A declared joined-result row keeps this report-order test live to run-5.
     * The ordinary run-3 snapshot is empty and the selected stop would end there.
     * No transfer of the real program or its engine stores is changed.
     */
    private fun selectedCheckpoint(f: DriverFixtures, config: RunConfig, key: MethodKey): RunMethodAnalyzer {
        val port = object : RunnerPort<RunMethodAnalyzer> {
            override val config = config
            override val shared = f.shared
            override val forms = shared.contexts.directed(config.direction)
            override val ops = f.ops
            override val steps = ProtocolSteps.Inline
            override fun send(event: RunEvent): Boolean = error("A frozen checkpoint sends no work")
            override fun post(event: RunEvent.Delivery): Boolean = error("A frozen checkpoint receives no work")
            override fun enqueue(analyzer: RunMethodAnalyzer): Boolean = error("A checkpoint has no queued input")
            override fun analyzer(key: MethodKey): RunMethodAnalyzer = error("A checkpoint has no actor lookup")
            override fun summaryStorage(key: MethodKey): SummaryStorage = error("A checkpoint has no subscriptions")
            override fun subscribe(sub: Subscription): Unit = error("A checkpoint has no subscriptions")
            override fun link(callee: MethodKey, ref: CallerRef, linkLayer: Layer, added: Facts): Unit =
                error("A checkpoint has no input links")
            override fun startInitials(callee: MethodKey, initials: Collection<InitialAp>): Unit =
                error("A checkpoint has no initial delivery")
        }
        val actor = RunMethodAnalyzer(key, port, PublicationSink { _, _ -> error("No publication work") },
            MethodLocalServicesFactory(::RunMethodLocalServices), MethodCallServicesFactory(::RunMethodCallServices))
        val initial = f.manager.initial(f.program.pattern(AccessPathBase.Argument(0)))
        val target = f.manager.factsOf(f.program.pattern(AccessPathBase.Return, tail = Tail.ANY).fact,
            ExclusionSet.Empty, Layer.DEMAND)
        actor.summaries.add(initial, target)
        actor.summaries.addDemand(initial, target)
        actor.freeze()
        return actor
    }

    @Test
    fun `a final earlier confirmation suppresses latest demand only evidence and its seed before the stop decision`(): Unit {
        DriverFixtures().use { f ->
            val confirmed = f.confirmed()
            val pending = f.persistentDemand()
            val checkpoint = f.program.method("selected barrier checkpoint", listOf(listOf(1), emptyList()), 1).key()
            val callbacks = ArrayList<Int>()
            var firstWitness: SinkWitness? = null
            var injected: SinkWitness? = null
            val policy = object : IterationPolicy {
                override fun fieldLimit(runIndex: Int): Int = maxOf(1, runIndex - 1)
                override fun continueAfter(run: RunConfig, result: RunResult<RunMethodAnalyzer>, frontiers: List<Frontier>): Boolean {
                    callbacks += run.index
                    assertTrue(run.index in listOf(1, 3), "STOP_RULE must precede a run-5 policy callback")
                    assertEquals(if (run.index == 1) 0 else 1, frontiers.last().confirmedVulnerabilities)
                    assertEquals(if (run.index == 1) 2 else 1, frontiers.last().demandVulnerabilities)
                    return true
                }
            }
            val driver = f.driver(policy, budget = 10.seconds, invokeRun = { config, owner, timeout ->
                val actual = f.run(config, owner, timeout)
                assertEquals(RunStatus.COMPLETE, actual.status)
                if (config.index == 3) {
                    assertEquals(setOf(confirmed.rule, pending.rule), actual.witnessesByKey().keys.map { it.rule }.toSet())
                    firstWitness = actual.witnessesByKey().entries.single { it.key.rule === confirmed.rule }.value.single()
                    // This test supplies an independent certificate at the joined-result seam.
                    // NORMAL alone is deliberately insufficient in the minimal driver.
                    assertNotNull(firstWitness).confirmed = true
                    // Prescribe independent selected support so the new empty-demand
                    // stop does not mask the intended later report-order regression.
                    val support = selectedCheckpoint(f, config, checkpoint)
                    return@driver RunResult(actual.status, actual.analyzers + support,
                        actual.runIndex, actual.direction, actual.vulnerabilities)
                }
                if (config.index != 5) actual else {
                    val actualRows = actual.witnessesByKey()
                    assertEquals(setOf(pending.rule), actualRows.keys.map { it.rule }.toSet(),
                        "The unchanged real engine must still have exactly its persistent DEMAND finding")
                    assertTrue(actualRows.values.flatten().all { it.edges.any { edge -> edge.layer == Layer.DEMAND } })
                    assertTrue(actual.demandLayerEdges > 0L, "The latest witness still has actual demand work")
                    val key = VulnerabilityKey(confirmed.rule, confirmed.root.method, confirmed.sink)
                    val demandFacts = f.ops.targetTree(confirmed.source.to, Layer.DEMAND)
                    val latest = SinkWitness(0, confirmed.root,
                        listOf(SinkEdge(f.manager.zero, Layer.DEMAND, demandFacts)), config.index)
                    injected = latest
                    // Only witness enumeration is replaced. Actual joined/frozen actors and every engine store stay intact.
                    val view = object : VulnerabilityStore {
                        override fun add(key: VulnerabilityKey, witness: SinkWitness): Unit = error("The complete-run view is read only")
                        override fun witnessesOf(run: Int): Sequence<Pair<VulnerabilityKey, SinkWitness>> =
                            if (run == 5) sequenceOf(key to latest) else actual.vulnerabilities.witnessesOf(run)
                    }
                    RunResult(actual.status, actual.analyzers, actual.runIndex, actual.direction, view)
                }
            })
            val report = driver.analyze(listOf(confirmed.root, pending.root))
            assertEquals(listOf(1, 2, 3, 4, 5), f.configs.map { it.index })
            assertEquals(listOf(1, 3), callbacks)
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 5, Direction.FORWARD, EndReason.STOP_RULE), report.end)
            val entry = report.entries.single()
            assertSame(confirmed.rule, entry.key.rule)
            assertEquals(ReportState.CONFIRMED, entry.state)
            assertEquals(3, entry.run)
            assertSame(firstWitness, entry.witnesses.single())
            assertTrue(entry.witnesses.single().confirmed)
            assertFalse(assertNotNull(injected).confirmed, "The minimal driver must not confirm the injected latest DEMAND edge")
            assertEquals(listOf(1, 2, 3, 4, 5), driver.frontiers.map { it.run })
            val final = driver.frontiers.last()
            assertEquals(1, final.confirmedVulnerabilities)
            assertEquals(0, final.demandVulnerabilities)
            assertEquals(0, final.seeds, "A final prior CONFIRMED key cannot create a sink seed from latest DEMAND evidence")
            assertTrue(f.results.last().demandLayerEdges > 0L)
            assertTrue(f.configs[3].seeds.at(confirmed.root, confirmed.sink).isEmpty())
            assertTrue(f.configs[3].seeds.at(pending.root, pending.sink).isNotEmpty())
        }
    }
}
