package org.opentaint.dataflow.jvm.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.path.TracePathGenerationResult
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.jvm.TaintSinkMeta
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.bidi.fixtures.JIRPrescanFixtures
import org.opentaint.dataflow.jvm.bidi.fixtures.NoTaintRules
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Final output reads settled report descriptors, without witness trees or trace resolution. */
class JIRBidiOutputTest : BidiJIRTestUtils() {
    private data class Context(val name: String) : MethodContext

    private fun entry(): BidiEntry = JIRBidiAnalysis(cp, graph, object : JIRUnitResolver {
        override fun resolve(method: JIRMethod) = SingletonUnit
        override fun locationIsUnknown(loc: RegisteredLocation): Boolean = false
    }, NoTaintRules, JIRAnalysisManager.Params(
        aliasAnalysisParams = JIRLocalAliasAnalysis.Params(useAliasAnalysis = false)), FixedLimits(listOf(1, 1, 2)), RefManager())

    private fun rule(id: String): RuleId = object : CommonTaintConfigurationSink {
        override val id: String = id
        override val meta = TaintSinkMeta("output $id", CommonTaintConfigurationSinkMeta.Severity.Warning, null)
    }

    private val catalog = ReportCatalog()

    private fun reportEntry(id: String, context: String): Report.Entry {
        val method = method("copy")
        val rule = rule(id)
        val reportId = catalog.intern(SinkKey(method, normalExit(method), id), rule,
            key(method, Context(context)))
        return Report.Entry(reportId, catalog.descriptor(reportId))
    }

    @Test
    fun `settled report identities become their exact sink rule with a simple trace`(): Unit {
        val first = reportEntry("first", "first context")
        val second = reportEntry("second", "second context")
        val report = Report(listOf(first, second), AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.NO_DEMAND_EDGE))
        val output = entry().toVulnerabilities(report)
        assertEquals(listOf("first", "second"), output.map { it.vulnerability.ruleId })
        for ((expected, actual) in report.entries.zip(output)) {
            val descriptor = expected.descriptor
            assertSame(descriptor.key.statement, actual.vulnerability.statement)
            assertSame(descriptor.rule, actual.vulnerability.rule)
            assertEquals(setOf(descriptor.rule), actual.vulnerability.vulnerabilityRules.keys)
            assertSame(TracePathGenerationResult.Simple, actual.trace)
            val node = assertIs<TaintSinkTracker.TaintVulnerabilityRuleNode.Unconditional>(
                actual.vulnerability.vulnerabilityRules.getValue(descriptor.rule))
            assertSame(descriptor.representativeMethodKey, node.methodEntryPoint)
        }
    }

    @Test
    fun `output uses the descriptor representative full context`(): Unit {
        val item = reportEntry("selected context", "representative context")
        val report = Report(listOf(item), AnalysisEnd(RunStatus.COMPLETE, 3, Direction.FORWARD, EndReason.NO_DEMAND_EDGE))
        val output = entry().toVulnerabilities(report).single()
        val node = assertIs<TaintSinkTracker.TaintVulnerabilityRuleNode.Unconditional>(
            output.vulnerability.vulnerabilityRules[item.descriptor.rule])
        assertSame(item.descriptor.representativeMethodKey, node.methodEntryPoint)
        assertEquals(Context("representative context"), node.methodEntryPoint.context)
        assertSame(item.descriptor.key.statement, output.vulnerability.statement)
        assertSame(TracePathGenerationResult.Simple, output.trace)
    }

    @Test
    fun `the same physical sink keeps its identity and representative context across rediscovery`(): Unit {
        val first = reportEntry("same sink", "first context")
        val later = reportEntry("same sink", "later context")
        assertEquals(first.id, later.id)
        assertSame(first.descriptor, later.descriptor)
        val report = Report(listOf(later), AnalysisEnd(RunStatus.COMPLETE, 5, Direction.FORWARD, EndReason.NO_DEMAND_EDGE))
        val output = entry().toVulnerabilities(report).single()
        val node = assertIs<TaintSinkTracker.TaintVulnerabilityRuleNode.Unconditional>(
            output.vulnerability.vulnerabilityRules[first.descriptor.rule])
        assertSame(first.descriptor.representativeMethodKey, node.methodEntryPoint)
        assertEquals(Context("first context"), node.methodEntryPoint.context)
    }

    @Test
    fun `all four statuses map exactly while retained settled report identities stay in output`(): Unit {
        val expected = mapOf(
            RunStatus.COMPLETE to TaintAnalysisUnitRunnerManager.Status.OK,
            RunStatus.TIMEOUT to TaintAnalysisUnitRunnerManager.Status.TIMEOUT,
            RunStatus.OOM to TaintAnalysisUnitRunnerManager.Status.OOM,
            RunStatus.FAILED to TaintAnalysisUnitRunnerManager.Status.EXCEPTION,
        )
        val entries = listOf(reportEntry("retained first", "first"), reportEntry("retained second", "second"))
        val converter = entry()
        for ((status, mapped) in expected) {
            val report = Report(entries, AnalysisEnd(status, 3, Direction.FORWARD,
                if (status == RunStatus.COMPLETE) EndReason.POLICY else EndReason.ABNORMAL))
            assertEquals(mapped, converter.status(report))
            val output = converter.toVulnerabilities(report)
            assertEquals(setOf("retained first", "retained second"), output.map { it.vulnerability.ruleId }.toSet())
            assertTrue(output.all { it.trace === TracePathGenerationResult.Simple })
        }
    }

    @Test
    fun `an incomplete first run converts its empty real report to no output and preserves its cause`(): Unit {
        val converter = entry()
        for ((status, mapped) in listOf(
            RunStatus.TIMEOUT to TaintAnalysisUnitRunnerManager.Status.TIMEOUT,
            RunStatus.OOM to TaintAnalysisUnitRunnerManager.Status.OOM,
            RunStatus.FAILED to TaintAnalysisUnitRunnerManager.Status.EXCEPTION,
        )) {
            val report = Report(emptyList(), AnalysisEnd(status, 1, Direction.FORWARD, EndReason.ABNORMAL))
            assertTrue(converter.toVulnerabilities(report).isEmpty())
            assertEquals(mapped, converter.status(report))
        }
    }

    @Test
    fun `the JVM entry requires gather and consumes the copied prescan once for a real empty program run`(): Unit {
        val converter = entry()
        assertFailsWith<IllegalStateException> { converter.run(5.seconds) }
        JIRPrescanFixtures(cp, graph).use { f ->
            assertFailsWith<IllegalStateException> { f.engine.requirePrescanJoined() }
            f.run()
            f.engine.requirePrescanJoined()
            converter.gather(f.manager, emptyList(), f.engine.prescanResolvedGraph())
            f.manager.releasePrescan()
            f.engine.releasePrescan()
            assertTrue(f.engine.allUnits().isEmpty())
            assertFailsWith<IllegalStateException> { f.engine.apManager }
            val report = converter.run(5.seconds)
            assertEquals(AnalysisEnd(RunStatus.COMPLETE, 1, Direction.FORWARD, EndReason.NO_DEMAND_EDGE), report.end)
            assertTrue(report.entries.isEmpty())
            assertTrue(converter.toVulnerabilities(report).isEmpty())
            assertEquals(TaintAnalysisUnitRunnerManager.Status.OK, converter.status(report))
            assertFailsWith<IllegalStateException> { converter.run(5.seconds) }
        }
    }
}
