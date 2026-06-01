package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.python.rules.TaintRules.Sink
import org.opentaint.dataflow.python.rules.TaintRules.Source
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ClassFeatureFlowTest : AnalysisTest() {

    // --- SimpleObject.py ---

    @Test
    fun testClassMethodCall() = assertSinkReachable(
        source = Source("SimpleObject.source", "taint", PositionBase.Result),
        sink = Sink("SimpleObject.sink", "taint", PositionBase.Argument(0), "class"),
        entryPointFunction = "SimpleObject.class_method_call"
    )

    @Test
    fun testClassMethodReturn() = assertSinkReachable(
        source = Source("SimpleObject.source", "taint", PositionBase.Result),
        sink = Sink("SimpleObject.sink", "taint", PositionBase.Argument(0), "class"),
        entryPointFunction = "SimpleObject.class_method_return"
    )

    // --- StaticMethod.py ---

    @Test
    fun testStaticMethodCall() = assertSinkReachable(
        source = Source("StaticMethod.source", "taint", PositionBase.Result),
        sink = Sink("StaticMethod.sink", "taint", PositionBase.Argument(0), "static"),
        entryPointFunction = "StaticMethod.static_method_call"
    )

    @Test
    fun testClassmethodCall() = assertSinkReachable(
        source = Source("StaticMethod.source", "taint", PositionBase.Result),
        sink = Sink("StaticMethod.sink", "taint", PositionBase.Argument(0), "static"),
        entryPointFunction = "StaticMethod.classmethod_call"
    )

    // --- ReceiverSelf.py ---

    // The receiver carries a tainted field into an instance method via `self`:
    // the receiver maps to the callee's self = Argument(0), and the prologue
    // assign exposes `self.data` to the body's sink.
    @Test
    fun testReceiverFieldToSelf() = assertSinkReachable(
        source = Source("ReceiverSelf.source", "taint", PositionBase.Result),
        sink = Sink("ReceiverSelf.sink", "taint", PositionBase.Argument(0), "receiver-self"),
        entryPointFunction = "ReceiverSelf.receiver_field_to_self"
    )

    // --- ResidualField.py ---

    // Regression for the abstract-read both-ends refinement (see ResidualField.py).
    @Test
    fun testReceiverResidualFieldAfterRead() = assertSinkReachable(
        source = Source("ResidualField.source", "taint", PositionBase.Result),
        sink = Sink("ResidualField.sink", "taint", PositionBase.Argument(0), "residual"),
        entryPointFunction = "ResidualField.receiver_residual_field"
    )
}
