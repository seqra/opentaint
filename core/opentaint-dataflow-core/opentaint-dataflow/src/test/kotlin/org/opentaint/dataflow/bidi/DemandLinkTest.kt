package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.engine.Target

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
    fun `DLINK retains provisional sink guidance and refines its normal report by run7`(): Unit {
        DriverFixtures().use { f ->
            val program = f.demandLink()
            val driver = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4, 5, 6)))
            val report = driver.analyze(listOf(program.root))
            println("DLINK_RELATIVE runs=${f.configs.map { it.index }} end=${report.end} findings=${report.entries.size} " +
                "frontiers=${driver.frontiers.map { listOf(it.run, it.demandEdges.values.sum(), it.targetDemand, it.seeds) }}")
            val argument = AccessPathBase.Argument(0)
            val mark = MarkSlot.Concrete(program.mark)
            val coarseLink = Pattern(PathFact(argument, emptyList(), Tail.ANY_TAINT, mark), ExclusionSet.Empty)
            assertEquals(listOf(1, 2, 3, 4, 5, 6, 7), f.configs.map { it.index })
            assertEquals(listOf(1, 1, 2, 3, 4, 5, 6), f.configs.map { it.fieldLimit })
            assertTrue(f.results.all { it.status == RunStatus.COMPLETE })
            val runThree = f.results[2]
            val stored = f.processed.filter { it.run == 3 }
            assertTrue(stored.isNotEmpty())
            assertTrue(stored.any { it.method == program.sinkMethod && it.delta.facts.layer == Layer.DEMAND },
                "The coarse caller's exact admission remains DEMAND inside the sink method")
            assertTrue(runThree.analyzers.all { actor -> actor.summaries.all().all { it.second.layer == Layer.NORMAL } })
            val mThree = runThree.analyzers.single { it.key == program.sinkMethod }
            val demandLinks = f.links(3, mThree.key).asSequence().filter { it.linkLayer == Layer.DEMAND }.toList()
            assertTrue(demandLinks.isNotEmpty(), "The primitive root EXACT cleaner demotes the layer while retaining the must payload")
            assertTrue(demandLinks.any { it.addedFact == coarseLink })
            assertTrue(runThree.demandLayerEdges > 0,
                "Real DEMAND starts are counted; raw incoming presence is still not stored")
            assertTrue(mThree.summaries.all().none(), "The throwing method has no reached normal exit summary")
            val terminal = mThree.targets.single()
            assertSame(Target.DemandTarget, terminal.target)
            assertFalse(terminal.premise.isZero)
            assertTrue(runThree.analyzers.filter { it.key == program.root }.all { actor ->
                actor.targets.none { it.premise.isZero && it.target is Target.NormalTarget }
            }, "A DEMAND caller cannot apply a NORMAL terminal relation")
            val coarseDemand = Pattern(PathFact(argument, listOf(program.q), Tail.ANY, mark), ExclusionSet.Empty)
            assertContains(f.configs[2].demand!!.near(program.reader, demandProbe(argument, listOf(program.q, program.r), mark))
                .map { it.entry }, coarseDemand)
            assertTrue(driver.frontiers.last().demandEdges.isEmpty())
            assertEquals(program.rule, report.entries.single().descriptor.rule,
                "The source taints descendants; cleaning only the root must not lose the g.h finding")
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 7, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertEquals(listOf(1, 2, 3, 4, 5, 6, 7), driver.frontiers.map { it.run })
            assertTrue(driver.frontiers[2].targetDemand > 0)
            assertTrue(driver.frontiers[2].seeds > 0)
            assertEquals(0, driver.frontiers.last().targetDemand)
            assertEquals(0, driver.frontiers.last().seeds)
            assertEquals(1, driver.frontiers.last().reportedSinks)
        }
    }
}
