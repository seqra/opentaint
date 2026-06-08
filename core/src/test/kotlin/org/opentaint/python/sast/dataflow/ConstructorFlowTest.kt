package org.opentaint.python.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.python.Argument
import org.opentaint.dataflow.configuration.python.Result
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ConstructorFlowTest : AnalysisTest() {

    // --- ConstructorArgFlow.py ---

    // Tainted constructor argument is stepped into __init__ and reaches the sink there.
    @Test
    fun testConstructorArgToSink() = assertSinkReachable(
        source = source("ConstructorArgFlow.source", "taint", Result),
        sink = sink("ConstructorArgFlow.sink", "taint", Argument(0), "ctor"),
        entryPointFunction = "ConstructorArgFlow.ctor_arg_to_sink"
    )

    // A sink rule keyed on the bare class QN (no __init__) still matches the
    // resolved MyService.__init__ via the matcher's .__init__ strip.
    @Test
    fun testConstructorClassQnSink() = assertSinkReachable(
        source = source("ConstructorArgFlow.source", "taint", Result),
        sink = sink("ConstructorArgFlow.MyService", "taint", Argument(0), "ctor"),
        entryPointFunction = "ConstructorArgFlow.ctor_arg_to_sink"
    )

    // No __init__ body: class-QN fallback in the reconstructor; result-type
    // binding still resolves `obj.handle(...)` to NoInitService.handle.
    @Test
    fun testNoInitClassChainedMethod() = assertSinkReachable(
        source = source("ConstructorArgFlow.source", "taint", Result),
        sink = sink("ConstructorArgFlow.sink", "taint", Argument(0), "ctor"),
        entryPointFunction = "ConstructorArgFlow.no_init_chained_method"
    )

    // Class-QN constructor sink must not fire when arg(0) is untainted, even
    // though a source was produced elsewhere in the entry point.
    @Test
    fun testConstructorClassQnSinkNotReachableWhenArgUntainted() = assertSinkNotReachable(
        source = source("ConstructorArgFlow.source", "taint", Result),
        sink = sink("ConstructorArgFlow.MyService", "taint", Argument(0), "ctor"),
        entryPointFunction = "ConstructorArgFlow.ctor_untainted_arg"
    )

    // --- ConstructorFieldFlow.py ---

    // Tainted ctor arg stored on `self.value` in __init__ surfaces on the
    // constructed object `b` and reaches the sink via `b.value`. Exercises the
    // constructor self↔constructed-object binding in PIRDSUAliasAnalysis.
    @Test
    fun testConstructorFieldToSink() = assertSinkReachable(
        source = source("ConstructorFieldFlow.source", "taint", Result),
        sink = sink("ConstructorFieldFlow.sink", "taint", Argument(0), "field"),
        entryPointFunction = "ConstructorFieldFlow.ctor_field_to_sink"
    )

    // --- ConstructorFieldViaMethod.py ---

    // Field set in __init__ from a tainted arg, then read in a SEPARATE method
    // via self. Minimal mirror of owasp request_wrapper (BenchmarkTest00283).
    @Test
    fun testConstructorFieldViaMethod() = assertSinkReachable(
        source = source("ConstructorFieldViaMethod.source", "taint", Result),
        sink = sink("ConstructorFieldViaMethod.sink", "taint", Argument(0), "via-method"),
        entryPointFunction = "ConstructorFieldViaMethod.ctor_field_via_method"
    )
}
