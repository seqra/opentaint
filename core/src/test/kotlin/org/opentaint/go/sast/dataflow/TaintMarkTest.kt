package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class TaintMarkTest : AnalysisTest() {

    private fun source(function: String, mark: String) = GoSerializedRule.Source(
        pkg = GoNameMatcher.Simple(function.substringBeforeLast('.', "")),
        function = GoNameMatcher.Simple(function.substringAfterLast('.')),
        condition = null,
        taint = listOf(GoSerializedAssignAction(mark, PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
    )

    private fun sink(function: String, mark: String, id: String) = GoSerializedRule.Sink(
        pkg = GoNameMatcher.Simple(function.substringBeforeLast('.', "")),
        function = GoNameMatcher.Simple(function.substringAfterLast('.')),
        condition = GoSerializedCondition.ContainsMark(mark, PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = id,
        meta = GoSinkMetaData("Taint sink: $function"),
        info = null,
    )

    private val sourceMarkA = source("test/util.SourceA", "markA")
    private val sourceMarkB = source("test/util.SourceB", "markB")
    private val sinkMarkA = sink("test/util.SinkA", "markA", "test-mark-a")
    private val sinkMarkB = sink("test/util.SinkB", "markB", "test-mark-b")

    @Test fun taintMarkMatch001T() = assertSinkReachable(sourceMarkA, sinkMarkA, "test.taintMarkMatch001T")
    @Test fun taintMarkMismatch001F() = assertSinkNotReachable(sourceMarkA, sinkMarkB, "test.taintMarkMismatch001F")
    @Test fun taintMarkMatch002T() = assertSinkReachable(sourceMarkB, sinkMarkB, "test.taintMarkMatch002T")
}
