package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.fixtures.demandProbe
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.store.VulnerabilityKey
import kotlin.test.*

class DemandLinkTest {
    @Test
    fun `DLINK retains the run3 demand link and stops with an unresolved candidate when outgoing support is empty`(): Unit {
        DriverFixtures().use { f ->
            val program = f.demandLink()
            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4, 5, 6)))
            val report = driver.analyze(listOf(program.root))
            val argument = AccessPathBase.Argument(0)
            val mark = MarkSlot.Concrete(program.mark)
            val coarseLink = Pattern(PathFact(argument, emptyList(), Tail.ANY_TAINT, mark), ExclusionSet.Empty)
            assertEquals(listOf(1, 2, 3), f.configs.map { it.index })
            assertEquals(listOf(1, 1, 2), f.configs.map { it.fieldLimit })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            val runThree = f.results[2]
            val stored = f.processed.filter { it.run == 3 }
            assertTrue(stored.isNotEmpty())
            assertTrue(stored.all { it.delta.facts.layer == Layer.NORMAL },
                "At limit 2 every processed delta is normal; a coarse link is the remaining demand object")
            assertTrue(runThree.analyzers.all { actor -> actor.summaries.all().all { it.second.layer == Layer.NORMAL } })
            val mThree = runThree.analyzers.single { it.key == program.sinkMethod }
            val demandLinks = f.links(3, mThree.key).asSequence().filter { it.linkLayer == Layer.DEMAND }.toList()
            assertTrue(demandLinks.isNotEmpty(), "The primitive root EXACT cleaner demotes the layer while retaining the must payload")
            assertTrue(demandLinks.any { it.addedFact == coarseLink })
            assertEquals(0L, runThree.demandLayerEdges,
                "Restricted initial packets do not retain the removed raw-input-presence diagnostic")
            assertTrue(mThree.summaries.all().none(), "The throwing method has no reached normal exit summary")
            val key = VulnerabilityKey(program.rule, program.sinkMethod.method, program.sink)
            val witnesses = runThree.witnessesByKey().getValue(key)
            assertTrue(witnesses.all { !it.confirmed }, "Normal concrete emission cannot confirm through a demand link")
            assertTrue(witnesses.any { witness -> witness.edges.all { it.layer == Layer.NORMAL } })
            assertTrue(runThree.witnessesByKey().getValue(key).any { witness ->
                witness.edges.any { edge -> f.ops.leaves(edge.facts).any { it.fact.tail != Tail.EXACT } }
            }, "The run-2 limit-one guide still permits a coarse normal must answer in run-3")
            val coarseDemand = Pattern(PathFact(argument, listOf(program.q), Tail.ANY, mark), ExclusionSet.Empty)
            assertContains(f.configs[2].demand!!.near(program.reader, demandProbe(argument, listOf(program.q, program.r), mark))
                .map { it.entry }, coarseDemand)
            assertTrue(driver.frontiers.last().demandEdges.isEmpty())
            assertTrue(runThree.witnessesByKey().getValue(key).all { !it.confirmed })
            assertEquals(ReportState.DEMAND, report.entries.single { it.key == key }.state)
            assertEquals(3, report.entries.single { it.key == key }.run)
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(listOf(1, 2, 3), driver.frontiers.map { it.run })
            assertEquals(1, driver.frontiers[2].demandVulnerabilities)
            assertEquals(1, driver.frontiers[2].seeds)
            assertEquals(0, driver.frontiers.last().confirmedVulnerabilities)
        }
    }
}
