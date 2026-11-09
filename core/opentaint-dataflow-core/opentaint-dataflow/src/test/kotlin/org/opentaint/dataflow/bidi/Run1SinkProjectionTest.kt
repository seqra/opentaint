package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

class Run1SinkProjectionTest {
    private fun rule() = object : CommonTaintConfigurationSink {
        override val id = "complete sink projection"
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = id
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }

    @Test fun `weak complete sink arms are DEMAND and retain every physical predicate seed`() {
        for (predicateSink in listOf(false, true)) MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val service = actor.localServices
            val p = f.pattern(AccessPathBase.Argument(0))
            val q = f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U")))
            val id = RuleOccurrenceId(FormKey(FormOwner(), f.key.method, f.key, f.inst(1)), RuleKind.EXIT_SINK, 0)
            val builder = RulePredicate.Builder(f.cancellation)
            val predicate = builder.build(builder.and(listOf(builder.leaf(p), builder.leaf(q))))
            val sink = if (predicateSink) SinkRule(rule(), 0, predicate.leaves, emptyList(), id, predicate)
                else SinkRule(rule(), 0, listOf(p, q), emptyList())
            val first = f.manager.initial(p)
            val second = f.manager.initial(q)
            service.checkSinks(first, f.inst(1), f.manager.factsOf(p.fact, p.exclusion, Layer.NORMAL), listOf(sink))
            assertTrue(actor.targets.isEmpty() && actor.sinkSeeds.isEmpty(), "A partial witness cannot publish")
            assertTrue(actor.reachedSinkReportIds.isEmpty(), "An incomplete ND cube is not a provisional finding")
            service.checkSinks(second, f.inst(1), f.manager.factsOf(q.fact, q.exclusion, Layer.NORMAL), listOf(sink))
            assertEquals(setOf(TargetSummary(first, Target.DemandTarget), TargetSummary(second, Target.DemandTarget)), actor.targets)
            val reached = actor.reachedSinkReportIds.single()
            assertEquals(f.inst(1), f.shared.reportCatalog.descriptor(reached).key.statement)
            if (predicateSink) {
                assertEquals(Seed.PredicateSink(id, f.key, f.inst(1)), actor.sinkSeeds.single())
            } else {
                assertEquals(setOf(p, q), actor.sinkSeeds.map { assertIs<Seed.Sink>(it).requirement }.toSet())
            }
        }
    }

    @Test fun `one retained origin and optional ZERO dependencies keep NORMAL while an uncertain input stays DEMAND`() {
        for (zeroSecond in listOf(false, true)) for (layer in Layer.entries) MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val p = f.pattern(AccessPathBase.Argument(0))
            val q = f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U")))
            val sink = SinkRule(rule(), 0, listOf(p, q), emptyList())
            val origin = f.manager.initial(p)
            actor.localServices.checkSinks(origin, f.inst(1), f.manager.factsOf(p.fact, p.exclusion, Layer.NORMAL), listOf(sink))
            actor.localServices.checkSinks(if (zeroSecond) f.manager.zero else origin, f.inst(1),
                f.manager.factsOf(q.fact, q.exclusion, layer), listOf(sink))
            val row = actor.targets.single()
            assertEquals(origin, row.premise)
            if (layer == Layer.NORMAL) {
                assertIs<Target.NormalTarget>(row.target)
                assertTrue(actor.sinkSeeds.isEmpty())
            } else {
                assertEquals(Target.DemandTarget, row.target)
                assertEquals(setOf(p, q), actor.sinkSeeds.map { assertIs<Seed.Sink>(it).requirement }.toSet())
            }
        }
    }

    @Test fun `same origin NORMAL and DEMAND sink results coexist in both arrival orders`() {
        for (layers in listOf(listOf(Layer.NORMAL, Layer.DEMAND), listOf(Layer.DEMAND, Layer.NORMAL)))
            MethodAnalysisFixtures().use { f ->
                val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
                val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
                val p = f.pattern(AccessPathBase.Argument(0))
                val q = f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U")))
                val sink = SinkRule(rule(), 0, listOf(p, q), emptyList())
                val origin = f.manager.initial(p)
                actor.localServices.checkSinks(origin, f.inst(1), f.manager.factsOf(q.fact, q.exclusion, Layer.NORMAL), listOf(sink))
                for (layer in layers) actor.localServices.checkSinks(origin, f.inst(1),
                    f.manager.factsOf(p.fact, p.exclusion, layer), listOf(sink))
                assertEquals(setOf(origin), actor.targets.map { it.premise }.toSet())
                assertEquals(1, actor.targets.count { it.target is Target.NormalTarget })
                assertEquals(1, actor.targets.count { it.target == Target.DemandTarget })
                assertEquals(1, actor.reachedSinkReportIds.size, "NORMAL and DEMAND share a physical reporting identity")
                assertEquals(setOf(p, q), actor.sinkSeeds.map { assertIs<Seed.Sink>(it).requirement }.toSet())
            }
    }

    @Test fun `all ZERO witnesses keep the joined layer and never require a nonzero origin`() {
        for (layer in Layer.entries) MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val p = f.pattern(AccessPathBase.Argument(0))
            val q = f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U")))
            val sink = SinkRule(rule(), 0, listOf(p, q), emptyList())
            actor.localServices.checkSinks(f.manager.zero, f.inst(1), f.manager.factsOf(p.fact, p.exclusion, Layer.NORMAL), listOf(sink))
            actor.localServices.checkSinks(f.manager.zero, f.inst(1), f.manager.factsOf(q.fact, q.exclusion, layer), listOf(sink))
            val row = actor.targets.single()
            assertTrue(row.premise.isZero)
            if (layer == Layer.NORMAL) assertIs<Target.NormalTarget>(row.target)
            else assertEquals(Target.DemandTarget, row.target)
        }
    }

    @Test fun `two partial FULL callers never report a direct conjunctive sink`() = DriverFixtures().use { f ->
        val c = f.unsupportedJoint()
        val report = f.driver(FixedLimits(listOf(1, 1, 2)), run1MarkMode = MarkMode.FULL).analyze(listOf(c.root))
        assertEquals(RunStatus.COMPLETE, report.end.status)
        assertTrue(report.entries.isEmpty(), "Each call lacks one required mark")
        val first = f.results.first().analyzers.single { it.key.method == c.sink.location.method }
        assertEquals(2, first.targets.size)
        assertTrue(first.targets.all { it.target == Target.DemandTarget })
        assertEquals(2, first.sinkSeeds.size, "Both original sink requirements must guide the backward run")
        val refined = f.results.first { it.runIndex >= 3 && it.direction == Direction.FORWARD }
        val callee = refined.analyzers.single { it.key.method == c.sink.location.method }
        assertTrue(callee.targets.any { it.target is Target.NormalTarget && it.premise.size == 2 },
            "The later local witness keeps its complete hypothetical ND premise")
        assertTrue(refined.analyzers.single { it.key == c.root }.targets.none {
            it.premise.isZero && it.target is Target.NormalTarget
        }, "Neither incomplete call can satisfy the complete normal terminal")
    }
}
