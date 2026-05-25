package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.mkTrue
import org.opentaint.dataflow.go.rules.GoAssignMark
import org.opentaint.dataflow.go.rules.GoRuleCondition
import org.opentaint.dataflow.go.rules.TaintRules
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SampleTest : AnalysisTest() {

    private fun source(function: String) = TaintRules.Source(
        function = function,
        condition = mkTrue(),
        actionsAfter = listOf(GoAssignMark("taint", PositionBaseWithModifiers.BaseOnly(Result))),
    )

    private fun sink(function: String, id: String) = TaintRules.Sink(
        function = function,
        condition = CommonCondition.Atom(GoRuleCondition.ContainsMark(PositionBaseWithModifiers.BaseOnly(Argument(0)), "taint")),
        trackFactsReachAnalysisEnd = emptyList(),
        id = id,
        meta = TaintRules.Sink.DefaultMeta("Taint sink: $function"),
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
