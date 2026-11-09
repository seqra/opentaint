package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import kotlin.test.*

/** Final reports contain settled root terminal IDs, not local sink witness candidates. */
class ReportTest {
    private fun rule(name: String) = object : CommonTaintConfigurationSink {
        override val id = name
        override val meta = object : CommonTaintConfigurationSinkMeta {
            override val message = name
            override val severity = CommonTaintConfigurationSinkMeta.Severity.Warning
        }
    }
    private fun id(f: MethodAnalysisFixtures, name: String = "sink", at: Int = 2,
                   owner: MethodKey = f.key): ReportId {
        val sink = rule(name)
        return f.shared.reportCatalog.intern(SinkKey(owner.method, f.inst(at), name), sink, owner)
    }
    private fun config(f: MethodAnalysisFixtures, run: Int = 1, roots: List<MethodKey> = listOf(f.key),
                       retained: NormalTargetView = NormalTargetView.EMPTY) = RunConfig(run, maxOf(1, run - 1),
        if (run == 1) null else DemandStore.Builder(f.manager).build(), f.records,
        SeedIndex.EMPTY, roots, normalTargets = retained)
    private fun actor(f: MethodAnalysisFixtures, c: RunConfig, owner: MethodKey = f.key,
                      vararg rows: TargetSummary): RunMethodAnalyzer = f.core(c, key = owner).also { actor ->
        for (row in rows) actor.emitTarget(row.premise, row.target)
        f.drain(actor)
        actor.freeze()
    }
    private fun result(c: RunConfig, vararg actors: RunMethodAnalyzer, status: RunStatus = RunStatus.COMPLETE) =
        RunResult(status, actors.toList(), c.index, c.direction)
    private fun end(run: Int = 1, status: RunStatus = RunStatus.COMPLETE, reason: EndReason = EndReason.POLICY) =
        AnalysisEnd(status, run, if (run % 2 == 1) Direction.FORWARD else Direction.BACKWARD, reason)

    @Test fun `catalog identity is location and configured rule id across contexts and bound rule objects`() {
        MethodAnalysisFixtures().use { f ->
            val first = id(f)
            assertEquals(first, id(f, owner = f.store.key("another context")))
            assertNotEquals(first, id(f, name = "other"))
            assertNotEquals(first, id(f, at = 1))
            val descriptor = f.shared.reportCatalog.descriptor(first)
            assertEquals("sink", descriptor.key.ruleId)
            assertEquals(f.inst(2), descriptor.key.statement)
            assertEquals(f.key.method, descriptor.representativeMethodKey.method)
        }
    }

    @Test fun `only configured root Zero normal targets produce final reports`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val conditionalId = id(f, "conditional")
            val nonroot = f.store.key("nonroot")
            val conditional = f.manager.initial(f.pattern())
            val c = config(f)
            val root = actor(f, c, f.key,
                TargetSummary(f.manager.zero, Target.NormalTarget(reportId)),
                TargetSummary(conditional, Target.NormalTarget(conditionalId)),
                TargetSummary(f.manager.zero, Target.DemandTarget))
            val other = actor(f, c, nonroot, TargetSummary(conditional, Target.NormalTarget(conditionalId)))
            builder.commit(builder.prepare(c, result(c, root, other), f.shared))
            val entry = builder.build(end()).entries.single()
            assertEquals(reportId, entry.id)
            assertEquals(1, builder.reportCount)
            assertTrue(builder.normalTargets.contains(f.key, conditional, conditionalId))
            assertTrue(builder.normalTargets.contains(nonroot, conditional, conditionalId))
        }
    }

    @Test fun `prepare has no observable effect until its entire snapshot is committed`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val c = config(f)
            val root = actor(f, c, f.key, TargetSummary(f.manager.zero, Target.NormalTarget(reportId)))
            val prepared = builder.prepare(c, result(c, root), f.shared)
            assertEquals(0, builder.reportCount)
            assertTrue(builder.normalTargets.rows().none())
            builder.commit(prepared)
            assertEquals(1, builder.reportCount)
            assertTrue(builder.normalTargets.contains(f.key, f.manager.zero, reportId))
        }
    }

    @Test fun `rooted settlement can cover a nonroot Zero row with the same id`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val c = config(f)
            val child = f.store.key("child")
            val row = TargetSummary(f.manager.zero, Target.NormalTarget(reportId))
            val root = actor(f, c, f.key, row)
            val nonroot = actor(f, c, child, row)
            builder.commit(builder.prepare(c, result(c, root, nonroot), f.shared))
            assertEquals(1, builder.reportCount)
            assertEquals(2, builder.normalTargets.zeroRows().count())
        }
    }

    @Test fun `unsettled nonroot Zero cannot be retained at a complete barrier`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val c = config(f)
            val nonroot = actor(f, c, f.store.key("child"),
                TargetSummary(f.manager.zero, Target.NormalTarget(reportId)))
            assertFailsWith<IllegalStateException> { builder.prepare(c, result(c, nonroot), f.shared) }
            assertEquals(0, builder.reportCount)
            assertTrue(builder.normalTargets.rows().none())
        }
    }

    @Test fun `retained exact keys suppress later publication and settled ids survive skipped runs`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val c1 = config(f)
            val row = TargetSummary(f.manager.zero, Target.NormalTarget(reportId))
            val root = actor(f, c1, f.key, row)
            builder.commit(builder.prepare(c1, result(c1, root), f.shared))
            val previous = builder.build(end())
            val c3 = config(f, 3, retained = builder.normalTargets)
            val repeated = actor(f, c3, f.key, row)
            assertTrue(repeated.targets.isEmpty())
            builder.commit(builder.prepare(c3, result(c3, repeated), f.shared))
            assertEquals(previous.entries, builder.build(end(3)).entries)
            val c5 = config(f, 5, retained = builder.normalTargets)
            builder.commit(builder.prepare(c5, result(c5), f.shared))
            assertEquals(previous.entries, builder.build(end(5)).entries)
        }
    }

    @Test fun `backward adds no report or retained normal terminal`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val c1 = config(f)
            builder.commit(builder.prepare(c1, result(c1,
                actor(f, c1, f.key, TargetSummary(f.manager.zero, Target.NormalTarget(reportId)))), f.shared))
            val before = builder.build(end())
            val c2 = config(f, 2, retained = builder.normalTargets)
            val backward = actor(f, c2, f.key,
                TargetSummary(f.manager.zero, Target.NormalTarget(id(f, "backward"))))
            assertTrue(backward.targets.isEmpty())
            builder.commit(builder.prepare(c2, result(c2, backward), f.shared))
            assertEquals(before.entries, builder.build(end(2)).entries)
        }
    }

    @Test fun `incomplete run preparation rejects all new evidence and preserves the last committed snapshot`() {
        for (status in listOf(RunStatus.TIMEOUT, RunStatus.OOM, RunStatus.FAILED)) MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val c1 = config(f)
            builder.commit(builder.prepare(c1, result(c1,
                actor(f, c1, f.key, TargetSummary(f.manager.zero, Target.NormalTarget(reportId)))), f.shared))
            val before = builder.build(end())
            val c3 = config(f, 3, retained = builder.normalTargets)
            assertFailsWith<IllegalStateException> { builder.prepare(c3, result(c3, status = status), f.shared) }
            assertEquals(before.entries, builder.build(end(3, status, EndReason.ABNORMAL)).entries)
        }
    }

    @Test fun `report snapshots are immutable and retain analysis end metadata`() {
        MethodAnalysisFixtures().use { f ->
            val reportId = id(f)
            val entry = Report.Entry(reportId, f.shared.reportCatalog.descriptor(reportId))
            val input = arrayListOf(entry)
            val termination = end(3, RunStatus.OOM, EndReason.ABNORMAL)
            val report = Report(input, termination)
            input.clear()
            assertSame(entry, report.entries.single())
            assertSame(termination, report.end)
            assertFailsWith<UnsupportedOperationException> { (report.entries as MutableList<Report.Entry>).clear() }
        }
    }
    @Test fun `run limit adds latest witnesses with confirmation priority and immutable preparation`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val confirmed = id(f, "confirmed")
            val candidate = id(f, "candidate")
            val late = id(f, "after prepare")
            val c = config(f, 11)
            val root = actor(f, c, f.key, TargetSummary(f.manager.zero, Target.NormalTarget(confirmed)))
            root.reachedSinkReportIds += confirmed
            root.reachedSinkReportIds += candidate
            val prepared = builder.prepare(c, result(c, root), f.shared)
            root.reachedSinkReportIds += late
            assertTrue(builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.isEmpty())
            builder.commit(prepared)
            val entries = builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.associateBy { it.id }
            assertEquals(setOf(confirmed, candidate), entries.keys)
            assertFalse(entries.getValue(confirmed).provisional)
            assertTrue(entries.getValue(candidate).provisional)
            assertEquals(1, builder.reportCount, "Frontier report count keeps its confirmed meaning")
        }
    }

    @Test fun `latest forward witnesses replace older candidates and backward does not replace them`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val old = id(f, "discarded")
            val current = id(f, "latest")
            val backwardOnly = id(f, "backward only")
            val c1 = config(f)
            val first = actor(f, c1).also { it.reachedSinkReportIds += old }
            builder.commit(builder.prepare(c1, result(c1, first), f.shared))
            val c2 = config(f, 2)
            val backward = actor(f, c2).also { it.reachedSinkReportIds += backwardOnly }
            builder.commit(builder.prepare(c2, result(c2, backward), f.shared))
            assertEquals(listOf(old), builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.map { it.id })
            val c11 = config(f, 11)
            val latest = actor(f, c11).also { it.reachedSinkReportIds += current }
            builder.commit(builder.prepare(c11, result(c11, latest), f.shared))
            assertEquals(listOf(current), builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.map { it.id })
            builder.commit(builder.prepare(c11, result(c11), f.shared))
            assertTrue(builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.isEmpty())
        }
    }

    @Test fun `provisional witnesses are hidden on early or abnormal endings`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val candidate = id(f)
            val c = config(f)
            val root = actor(f, c).also { it.reachedSinkReportIds += candidate }
            builder.commit(builder.prepare(c, result(c, root), f.shared))
            for (reason in EndReason.entries.filter { it != EndReason.RUN_LIMIT }) {
                assertTrue(builder.build(end(3, reason = reason)).entries.isEmpty(), reason.name)
            }
            for (status in listOf(RunStatus.TIMEOUT, RunStatus.OOM, RunStatus.FAILED)) {
                assertFailsWith<IllegalStateException> {
                    builder.prepare(config(f, 11), result(c, status = status), f.shared)
                }
                assertTrue(builder.build(end(11, status, EndReason.ABNORMAL)).entries.isEmpty())
            }
        }
    }

    @Test fun `conditional normal witness is provisional until a configured root confirms it`() {
        MethodAnalysisFixtures().use { f ->
            val builder = ReportBuilder()
            val reportId = id(f)
            val premise = f.manager.initial(f.pattern())
            val c = config(f)
            val conditional = actor(f, c, f.key, TargetSummary(premise, Target.NormalTarget(reportId)))
                .also { it.reachedSinkReportIds += reportId }
            builder.commit(builder.prepare(c, result(c, conditional), f.shared))
            assertTrue(builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.single().provisional)
            val c11 = config(f, 11, retained = builder.normalTargets)
            val confirmed = actor(f, c11, f.key, TargetSummary(f.manager.zero, Target.NormalTarget(reportId)))
                .also { it.reachedSinkReportIds += reportId }
            builder.commit(builder.prepare(c11, result(c11, confirmed), f.shared))
            val entry = builder.build(end(11, reason = EndReason.RUN_LIMIT)).entries.single()
            assertEquals(reportId, entry.id)
            assertFalse(entry.provisional)
        }
    }

    @Test fun `provisional catalog observation preserves the first normal representative`() {
        MethodAnalysisFixtures().use { f ->
            val catalog = f.shared.reportCatalog
            val provisionalRule = rule("sink")
            val normalRule = rule("sink")
            val provisionalContext = f.store.key("provisional context")
            val normalContext = f.store.key("normal context")
            val key = SinkKey(f.key.method, f.inst(1), "sink")
            val candidate = catalog.internReached(key, provisionalRule, provisionalContext)
            assertSame(provisionalRule, catalog.descriptor(candidate).rule)
            assertEquals(candidate, catalog.intern(key, normalRule, normalContext))
            assertSame(normalRule, catalog.descriptor(candidate).rule)
            assertEquals(normalContext, catalog.descriptor(candidate).representativeMethodKey)
            assertEquals(candidate, catalog.internReached(key, provisionalRule, provisionalContext))
            assertSame(normalRule, catalog.descriptor(candidate).rule)
            assertEquals(candidate, catalog.intern(key, rule("sink"), provisionalContext))
            assertSame(normalRule, catalog.descriptor(candidate).rule, "Later normal witnesses keep the first normal descriptor")
        }
    }

}
