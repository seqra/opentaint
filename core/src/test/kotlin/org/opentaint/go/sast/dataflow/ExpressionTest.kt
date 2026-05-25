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
class ExpressionTest : AnalysisTest() {

    private fun source(function: String) = TaintRules.Source(
        function = function,
        condition = mkTrue(),
        actionsAfter = listOf(GoAssignMark("taint", PositionBaseWithModifiers.BaseOnly(Result))),
    )

    private fun sink(function: String) = TaintRules.Sink(
        function = function,
        condition = CommonCondition.Atom(GoRuleCondition.ContainsMark(PositionBaseWithModifiers.BaseOnly(Argument(0)), "taint")),
        trackFactsReachAnalysisEnd = emptyList(),
        id = "test-id",
        meta = TaintRules.Sink.DefaultMeta("Taint sink: $function"),
    )

    private val intSource = source("test.sourceInt")
    private val intSink = sink("test.sinkInt")
    private val boolSource = source("test.sourceBool")
    private val boolSink = sink("test.sinkBool")

    // String concatenation
    @Test fun stringConcat001T() = assertReachable("test.stringConcat001T")
    @Test fun stringConcat002T() = assertReachable("test.stringConcat002T")
    @Test fun stringConcat003T() = assertReachable("test.stringConcat003T")
    @Test fun stringConcat004F() = assertNotReachable("test.stringConcat004F")

    // String concat assignment
    @Test fun stringConcatAssign001T() = assertReachable("test.stringConcatAssign001T")
    @Test fun stringConcatAssign002F() = assertNotReachable("test.stringConcatAssign002F")

    // Concat chain
    @Test fun stringConcatChain001T() = assertReachable("test.stringConcatChain001T")
    @Test fun stringConcatChain002F() = assertNotReachable("test.stringConcatChain002F")

    // Integer arithmetic (kills taint)
    @Test fun intArith001F() = assertSinkNotReachable(intSource, intSink, "test.intArith001F")
    @Test fun intArith002F() = assertSinkNotReachable(intSource, intSink, "test.intArith002F")

    // Boolean negation (kills taint)
    @Test fun boolNeg001F() = assertSinkNotReachable(boolSource, boolSink, "test.boolNeg001F")

    // Comparison (kills taint)
    @Test fun comparison001F() = assertSinkNotReachable(stdSource, boolSink, "test.comparison001F")
}
