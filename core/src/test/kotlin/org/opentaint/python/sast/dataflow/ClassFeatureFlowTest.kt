package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.Result
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ClassFeatureFlowTest : AnalysisTest() {

    // --- SimpleObject.py ---

    @Test
    fun testClassMethodCall() = assertSinkReachable(
        source = source("SimpleObject.source", "taint", Result),
        sink = sink("SimpleObject.sink", "taint", Argument(0), "class"),
        entryPointFunction = "SimpleObject.class_method_call"
    )

    @Test
    fun testClassMethodReturn() = assertSinkReachable(
        source = source("SimpleObject.source", "taint", Result),
        sink = sink("SimpleObject.sink", "taint", Argument(0), "class"),
        entryPointFunction = "SimpleObject.class_method_return"
    )

    // --- StaticMethod.py ---

    @Test
    fun testStaticMethodCall() = assertSinkReachable(
        source = source("StaticMethod.source", "taint", Result),
        sink = sink("StaticMethod.sink", "taint", Argument(0), "static"),
        entryPointFunction = "StaticMethod.static_method_call"
    )

    @Test
    fun testClassmethodCall() = assertSinkReachable(
        source = source("StaticMethod.source", "taint", Result),
        sink = sink("StaticMethod.sink", "taint", Argument(0), "static"),
        entryPointFunction = "StaticMethod.classmethod_call"
    )

    // --- ReceiverSelf.py ---

    // The receiver carries a tainted field into an instance method via `self`:
    // the receiver maps to the callee's self = Argument(0), and the prologue
    // assign exposes `self.data` to the body's sink.
    @Test
    fun testReceiverFieldToSelf() = assertSinkReachable(
        source = source("ReceiverSelf.source", "taint", Result),
        sink = sink("ReceiverSelf.sink", "taint", Argument(0), "receiver-self"),
        entryPointFunction = "ReceiverSelf.receiver_field_to_self"
    )

    // --- ResidualField.py ---

    // Regression for the abstract-read both-ends refinement (see ResidualField.py).
    @Test
    fun testReceiverResidualFieldAfterRead() = assertSinkReachable(
        source = source("ResidualField.source", "taint", Result),
        sink = sink("ResidualField.sink", "taint", Argument(0), "residual"),
        entryPointFunction = "ResidualField.receiver_residual_field"
    )
}
