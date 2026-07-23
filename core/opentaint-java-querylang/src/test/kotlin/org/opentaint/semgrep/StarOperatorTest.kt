package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle.PER_CLASS
import org.opentaint.semgrep.util.SampleBasedTest
import org.opentaint.semgrep.util.TestAnalysisRunner
import kotlin.test.Test

@TestInstance(PER_CLASS)
class StarOperatorTest : SampleBasedTest() {
    // The starred SOURCE ($*X = src()) taints the whole object and every field; a concrete
    // field read only inherits that taint once the any-accessor is unrolled to a field read.
    // Mirror the Go harness and enable unrolling for THIS sample only (StarSink/StarSanitizer
    // keep the default AnyAccessorDisabled). Removing the source `*` makes the Positive a false
    // negative, proving the star is load-bearing here.
    @Test
    fun `star source field flow`() =
        runTest<taint.StarSource>(unrollStrategy = TestAnalysisRunner.AnyAccessorEnabled)

    @Test
    fun `star sink any field`() = runTest<taint.StarSink>()

    @Test
    fun `star sanitizer clears field taint`() = runTest<taint.StarSanitizer>()

    @AfterAll
    fun close() {
        closeRunner()
    }
}
