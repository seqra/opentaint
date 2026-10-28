package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.parallel.ResourceLock
import org.junit.jupiter.api.parallel.Resources
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.MarkMode
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.configuration.jvm.serialized.*
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/** Exercise the production normal-exit drop and the actual joined caller inputs. */
@ResourceLock(Resources.SYSTEM_PROPERTIES)
class JIRKilledStaticWriterAcceptanceTest : AnalysisTest() {
    override val sourceFileExtension = "java"
    private val cls = "test.samples.bidi.KilledStaticWriterSample"
    private val mark = "killed-static-writer-T"
    private val sinkId = "returned-static-before-exit-drop"

    private fun position(base: PositionBase) = PositionBaseWithModifiers.BaseOnly(base)
    private fun staticOutput() = PositionBaseWithModifiers.WithModifiers(PositionBase.ClassStatic(cls),
        listOf(PositionModifier.Field(cls, "output", "java.lang.Object")))
    private fun config() = SerializedTaintConfig(
        source = listOf(SerializedRule.Source(functionMatcher(cls, "source"), taint = listOf(
            SerializedTaintAssignAction(mark, pos = position(PositionBase.Result))))),
        sink = listOf(SerializedRule.Sink(functionMatcher(cls, "sink"),
            condition = SerializedCondition.ContainsMark(mark, position(PositionBase.Argument(0))),
            id = sinkId)),
        // The normal JVM boundary drops the static part matched by its exit sink.
        // The returned value must still have its earlier write/read dependency.
        methodExitSink = listOf("writeRead", "writeReadUnmarked").map { name ->
            SerializedRule.MethodExitSink(functionMatcher(cls, name),
                condition = SerializedCondition.ContainsMark(mark, staticOutput()),
                id = "write-read-exit")
        },
    )

    private fun run(entry: String, mode: MarkMode): BidiAcceptanceResult {
        val property = "opentaint.bidi.run1MarkMode"
        val previous = System.getProperty(property)
        try {
            System.setProperty(property, mode.name)
            return runBidiAcceptance(config(), cls, entry, listOf(1, 1, 2))
        } finally {
            if (previous == null) System.clearProperty(property) else System.setProperty(property, previous)
        }
    }

    @Test fun `JVM killed ZERO static writer retains source guidance through two returning wrappers`() {
        for (mode in MarkMode.entries) for (entry in listOf("direct", "nested")) {
            val result = run(entry, mode)
            assertEquals(RunStatus.COMPLETE, result.report.end.status, "$entry/$mode")
            assertEquals(listOf(1, 2, 3), result.runs.map { it.index }, "$entry/$mode")
            assertTrue(result.runs.all { it.status == RunStatus.COMPLETE })
            assertTrue(result.witnesses.any { it.run == 1 && it.rule.id == sinkId },
                "The run-1 candidate must exist: $entry/$mode")
            assertTrue(result.witnesses.any { it.run == 3 && it.rule.id == sinkId },
                "Static demand completion must keep the real returned flow: $entry/$mode")
            assertTrue(result.output.any { it.vulnerability.ruleId == sinkId })
            val writer = result.method("writeRead")
            assertTrue(result.runs.first().rawSummaries.none { it.method == writer &&
                it.conclusion.value.base == AccessPathBase.ClassStatic },
                "The exit drop must remain effective; completion adds guidance only")
            assertTrue(result.runs[1].sourceHits.any { it.action != null && it.forwardTo.mark == mark },
                "Run-2 must reach the full-mark source action: $entry/$mode")
        }
    }

    @Test fun `JVM static completion does not create a source for an unmarked static write`() {
        for (mode in MarkMode.entries) {
            val result = run("noSource", mode)
            assertEquals(RunStatus.COMPLETE, result.report.end.status)
            assertTrue(result.report.entries.isEmpty())
            assertTrue(result.output.isEmpty())
        }
    }
}
