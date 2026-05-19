package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.go.rules.TaintRules
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class TaintMarkTest : AnalysisTest() {

    private val sourceMarkA = TaintRules.Source("test/util.SourceA", "markA", Result)
    private val sourceMarkB = TaintRules.Source("test/util.SourceB", "markB", Result)
    private val sinkMarkA = TaintRules.Sink("test/util.SinkA", "markA", Argument(0), "test-mark-a")
    private val sinkMarkB = TaintRules.Sink("test/util.SinkB", "markB", Argument(0), "test-mark-b")

    @Test fun taintMarkMatch001T() = assertSinkReachable(sourceMarkA, sinkMarkA, "test.taintMarkMatch001T")
    @Test fun taintMarkMismatch001F() = assertSinkNotReachable(sourceMarkA, sinkMarkB, "test.taintMarkMismatch001F")
    @Test fun taintMarkMatch002T() = assertSinkReachable(sourceMarkB, sinkMarkB, "test.taintMarkMatch002T")
}
