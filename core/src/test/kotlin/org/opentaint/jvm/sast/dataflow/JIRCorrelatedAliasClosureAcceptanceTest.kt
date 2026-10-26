package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.parallel.ResourceLock
import org.junit.jupiter.api.parallel.Resources
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.configuration.jvm.serialized.*
import kotlin.test.*

/** Real prescan, definitions, producer alias stages and call guards exercise both event orders. */
@ResourceLock(Resources.SYSTEM_PROPERTIES)
class JIRCorrelatedAliasClosureAcceptanceTest : AnalysisTest() {
    override val sourceFileExtension = "java"
    private val cls = "test.samples.bidi.CorrelatedAliasClosureSample"
    private val mark = "correlated-alias-T"
    private val sinkId = "correlated-alias-sink"
    private fun at(base: PositionBase) = PositionBaseWithModifiers.BaseOnly(base)
    private fun whole(base: PositionBase) = PositionBaseWithModifiers.WithModifiers(base, listOf(PositionModifier.AnyField))
    private fun nestedEntry() = PositionBaseWithModifiers.WithModifiers(PositionBase.Argument(0), listOf(
        PositionModifier.Field("$cls\$Box", "next", "$cls\$Box"),
        PositionModifier.Field("$cls\$Box", "value", "java.lang.Object"),
    ))

    private fun check(entry: String, entrySource: Boolean = false): BidiAcceptanceResult {
        val config = SerializedTaintConfig(
            source = listOf(
                SerializedRule.Source(functionMatcher(cls, "source"),
                    taint = listOf(SerializedTaintAssignAction(mark, pos = at(PositionBase.Result)))),
                SerializedRule.Source(functionMatcher(cls, "mark"),
                    taint = listOf(SerializedTaintAssignAction(mark, pos = whole(PositionBase.Argument(0))))),
            ),
            entryPoint = if (entrySource) listOf(SerializedRule.EntryPoint(functionMatcher(cls, entry),
                taint = listOf(SerializedTaintAssignAction(mark, pos = nestedEntry())))) else emptyList(),
            sink = listOf(SerializedRule.Sink(functionMatcher(cls, "sink"),
                condition = SerializedCondition.ContainsMark(mark, at(PositionBase.Argument(0))),
                id = sinkId, meta = SinkMetaData(note = sinkId))),
        )
        val property = "opentaint.bidi.run1MarkMode"
        val previous = System.getProperty(property)
        val r = try {
            System.setProperty(property, "FULL")
            runBidiAcceptance(config, cls, entry, listOf(1, 1, 2))
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property, previous)
        }
        assertEquals(RunStatus.COMPLETE, r.report.end.status, entry)
        assertTrue(r.runs.all { it.status == RunStatus.COMPLETE }, entry)
        assertEquals(setOf(sinkId), r.output.map { it.vulnerability.ruleId }.toSet(), entry)
        assertTrue(r.witnesses.any { it.rule.id == sinkId && it.run == 1 }, entry)
        return r
    }

    @Test fun `alias definition after mark is supplied by the definition`() { check("aliasAfterMark") }
    @Test fun `mark after alias is supplied by the source alias stage`() { check("markAfterAlias") }
    @Test fun `field alias definition after marked write retains the field`() { check("fieldAliasAfterMark") }
    @Test fun `marked field write after alias supplies the existing alias`() { check("fieldMarkAfterAlias") }
    @Test fun `later demanded alias target survives the identity arm`() {
        val result = check("laterDemandedAlias", entrySource = true)
        assertTrue(result.runs.any { it.index > 1 }, "The nested read must exercise the later demand path")
        assertTrue(result.witnesses.any { it.rule.id == sinkId && it.run > 1 },
            "The later full-mark phase must still observe the aliased target")
    }
}
