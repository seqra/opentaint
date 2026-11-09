package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

class ReachedSinkObservationTest {
    private fun rule() = object : CommonTaintConfigurationSink {
        override val id = "observed physical sink"
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = id
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }

    @Test fun `actual demand witness is observed without adding a normal Target or changing its seed`() {
        MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val pattern = f.pattern(AccessPathBase.Argument(0), tail = Tail.EXACT)
            val initial = f.manager.initial(pattern)
            val sink = SinkRule(rule(), 0, listOf(pattern), emptyList())
            actor.localServices.checkSinks(initial, f.inst(1),
                f.manager.factsOf(pattern.fact, pattern.exclusion, Layer.DEMAND), listOf(sink))
            val observed = actor.reachedSinkReportIds.single()
            assertEquals(SinkKey(f.key.method, f.inst(1), sink.rule.id), f.shared.reportCatalog.descriptor(observed).key)
            assertEquals(setOf(TargetSummary(initial, Target.DemandTarget)), actor.targets)
            assertEquals(pattern, assertIs<Seed.Sink>(actor.sinkSeeds.single()).requirement)
        }
    }

    @Test fun `different physical sink witnesses remain visible when anonymous Targets deduplicate`() {
        MethodAnalysisFixtures().use { f ->
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices))
            val pattern = f.pattern(AccessPathBase.Argument(0), tail = Tail.EXACT)
            val initial = f.manager.initial(pattern)
            val sink = SinkRule(rule(), 0, listOf(pattern), emptyList())
            for (at in listOf(1, 2)) actor.localServices.checkSinks(initial, f.inst(at),
                f.manager.factsOf(pattern.fact, pattern.exclusion, Layer.DEMAND), listOf(sink))
            assertEquals(setOf(TargetSummary(initial, Target.DemandTarget)), actor.targets,
                "Anonymous Target equality and propagation do not change")
            assertEquals(setOf(f.inst(1), f.inst(2)), actor.reachedSinkReportIds.map {
                f.shared.reportCatalog.descriptor(it).key.statement
            }.toSet(), "The report observer must retain both actual physical hits")
        }
    }

    @Test fun `nested loop block witnesses stay on the method owner and survive freeze`() {
        // while (outer()) { while (inner()) sinkT(p); }
        val graph = listOf(listOf(1), listOf(2, 5), listOf(3, 4), listOf(2), listOf(1), emptyList())
        MethodAnalysisFixtures(graph, normalExit = 5).use { f ->
            val base = AccessPathBase.Argument(0)
            val pattern = f.pattern(base, tail = Tail.EXACT)
            val sink = SinkRule(rule(), 0, listOf(pattern), emptyList())
            val identity = StatementSummary.identities(listOf(base))
            f.call(3, CallPlan(setOf(base), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, identity),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
            ), listOf(sink), BEFORE, AFTER))
            val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
            val actor = f.core(config, localFactory = MethodLocalServicesFactory(::RunMethodLocalServices),
                callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            actor.addInitial(f.manager.initial(pattern))
            f.drain(actor, quantum = 1)
            val witnessed = actor.reachedSinkReportIds.single()
            assertEquals(f.inst(3), f.shared.reportCatalog.descriptor(witnessed).key.statement)
            assertTrue(actor.joinedBlockStates().size > 2, "The sink was reached inside a decomposed nested loop")
            actor.freeze()
            assertEquals(setOf(witnessed), actor.reachedSinkReportIds)
            val builder = ReportBuilder()
            builder.commit(builder.prepare(config, RunResult(RunStatus.COMPLETE, listOf(actor), 1, Direction.FORWARD), f.shared))
            val entry = builder.build(AnalysisEnd(RunStatus.COMPLETE, 11, Direction.FORWARD, EndReason.RUN_LIMIT)).entries.single()
            assertEquals(witnessed, entry.id)
            assertTrue(entry.provisional, "A conditional local NORMAL witness is not a confirmed root-ZERO report")
        }
    }
}
