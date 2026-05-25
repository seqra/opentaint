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
class TaintMarkTest : AnalysisTest() {

    private fun source(function: String, mark: String) = TaintRules.Source(
        function = function,
        condition = mkTrue(),
        actionsAfter = listOf(GoAssignMark(mark, PositionBaseWithModifiers.BaseOnly(Result))),
    )

    private fun sink(function: String, mark: String, id: String) = TaintRules.Sink(
        function = function,
        condition = CommonCondition.Atom(GoRuleCondition.ContainsMark(PositionBaseWithModifiers.BaseOnly(Argument(0)), mark)),
        trackFactsReachAnalysisEnd = emptyList(),
        id = id,
        meta = TaintRules.Sink.DefaultMeta("Taint sink: $function"),
    )

    private val sourceMarkA = source("test/util.SourceA", "markA")
    private val sourceMarkB = source("test/util.SourceB", "markB")
    private val sinkMarkA = sink("test/util.SinkA", "markA", "test-mark-a")
    private val sinkMarkB = sink("test/util.SinkB", "markB", "test-mark-b")

    @Test fun taintMarkMatch001T() = assertSinkReachable(sourceMarkA, sinkMarkA, "test.taintMarkMatch001T")
    @Test fun taintMarkMismatch001F() = assertSinkNotReachable(sourceMarkA, sinkMarkB, "test.taintMarkMismatch001F")
    @Test fun taintMarkMatch002T() = assertSinkReachable(sourceMarkB, sinkMarkB, "test.taintMarkMatch002T")
}
