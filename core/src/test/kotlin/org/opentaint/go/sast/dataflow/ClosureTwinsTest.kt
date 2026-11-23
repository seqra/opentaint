package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * Closures of two methods with the same name share the short name and the signature.
 * A call of such a closure must reach the closure of its own method.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ClosureTwinsTest : AnalysisTest() {

    @Test fun funcValue() = assertTwins("closureTwinFuncValue")
    @Test fun capturedValue() = assertTwins("closureTwinCapturedValue")
    @Test fun nestedClosure() = assertTwins("closureTwinNestedClosure")
    @Test fun fieldWrite() = assertTwins("closureTwinFieldWrite")
    @Test fun mapKey() = assertTwins("closureTwinMapKey")

    private fun assertTwins(name: String) {
        val vulnerable = runAnalysis(stdSource, stdSink, "test.${name}001T").isNotEmpty()
        val safe = runAnalysis(stdSource, stdSink, "test.${name}002F").isNotEmpty()
        assertEquals(
            "001T reached=true, 002F reached=false",
            "001T reached=$vulnerable, 002F reached=$safe",
            "Sink reachability of $name",
        )
    }
}
