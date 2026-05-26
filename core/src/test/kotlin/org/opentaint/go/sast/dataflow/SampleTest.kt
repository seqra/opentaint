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
class SampleTest : AnalysisTest() {

    private fun source(function: String) = GoSerializedRule.Source(
        function = GoNameMatcher.Simple(function),
        condition = null,
        taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
        info = null,
    )

    private fun sink(function: String, id: String) = GoSerializedRule.Sink(
        function = GoNameMatcher.Simple(function),
        condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
        trackFactsReachAnalysisEnd = emptyList(),
        id = id,
        meta = GoSinkMetaData("Taint sink: $function"),
        info = null,
    )

    @Test
    fun sample() = assertSinkReachable(
        source("test/util.Source"),
        sink("test/util.Sink", "test-id"),
        "test.sample"
    )

    @Test
    fun sampleNonReachable() = assertSinkNotReachable(
        source("test/util.Source"),
        sink("test/util.Sink", "test-id"),
        "test.sampleNonReachable"
    )
}
