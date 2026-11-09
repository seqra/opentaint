package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.parallel.ResourceLock
import org.junit.jupiter.api.parallel.Resources
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import kotlin.test.assertEquals

/** These real paths must report. Keep the assertion if a current core gap prevents it. */
@ResourceLock(Resources.SYSTEM_PROPERTIES)
class MainMigrationBoundaryCoverageTest : AnalysisTest() {
    override val sourceFileExtension = "java"
    private val cls = "test.samples.bidi.MigrationBoundaryCoverageSample"
    private val mark = "migration-boundary-T"
    private val root = PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(0))
    private val below = PositionBaseWithModifiers.WithModifiers(PositionBase.Argument(0), listOf(PositionModifier.AnyField))

    private fun config(entrySource: String, cleanRoot: Boolean) = SerializedTaintConfig(
        entryPoint = listOf(SerializedRule.EntryPoint(functionMatcher(cls, entrySource), taint = buildList {
            add(SerializedTaintAssignAction(mark, pos = root))
            if (cleanRoot) add(SerializedTaintAssignAction(mark, pos = below))
        })),
        cleaner = if (cleanRoot) listOf(SerializedRule.Cleaner(functionMatcher(cls, "clean"),
            cleans = listOf(SerializedTaintCleanAction(mark, root)))) else emptyList(),
        sink = listOf(SerializedRule.Sink(functionMatcher(cls, "sink"),
            condition = SerializedCondition.ContainsMark(mark, root), id = "migration-boundary-sink")),
    )

    private fun check(entry: String, sourceAt: String = entry, cleanRoot: Boolean = true) {
        val property = "opentaint.bidi.run1MarkMode"
        val previous = System.getProperty(property)
        val result = try {
            System.setProperty(property, "FULL")
            runBidiAcceptance(config(sourceAt, cleanRoot), cls, entry, listOf(1) + (1..8).toList())
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property, previous)
        }
        val trace = buildString {
            appendLine("entry=$entry end=${result.report.end}")
            for (run in result.runs) {
                appendLine("run-${run.index} limit=${run.fieldLimit} ${run.direction}")
                appendLine("initials=${run.initials}")
                appendLine("processed=${run.processed}")
                appendLine("summaries=${run.rawSummaries}")
                appendLine("records=${run.records}")
                appendLine("targets=${run.targets}")
                appendLine("incomingSeeds=${run.incomingSeeds}")
                appendLine("outgoingDemand=${run.outgoingDemand}")
                appendLine("sourceHits=${run.sourceHits}")
                appendLine("sinkHits=${result.sinkHits.filter { it.run == run.index }}")
            }
        }
        assertEquals(RunStatus.COMPLETE, result.report.end.status, trace)
        assertEquals(setOf("migration-boundary-sink"), result.output.mapTo(linkedSetOf()) {
            it.vulnerability.ruleId
        }, trace)
    }

    @Test fun `entry-source descendants survive an exact root clean at one field`() {
        check("shallowAfterRootClean")
    }

    @Test fun `entry-source descendants survive an exact root clean at two fields`() {
        check("deepAfterRootClean")
    }

    @Test fun `entry-source mark reaches a static read in the same method`() {
        check("staticAfterEntrySource", cleanRoot = false)
    }

    @Test fun `a later static clear does not erase an earlier sink`() {
        check("rootWithClear", sourceAt = "staticAfterEntrySource", cleanRoot = false)
    }
}
