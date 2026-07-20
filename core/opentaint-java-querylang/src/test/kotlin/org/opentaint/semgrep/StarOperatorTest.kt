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

    // ---- Deep-nesting matrix: taint hidden 5+ fields deep and/or 5+ calls deep ----

    // Starred source, taint 5 fields deep, unhidden by a nested field read. Needs the
    // any-accessor unroll (like `star source field flow`) so the source star reaches a
    // concrete deep field read.
    @Test
    fun `star deep source field flow`() =
        runTest<taint.StarDeepSource>(unrollStrategy = TestAnalysisRunner.AnyAccessorEnabled)

    // Starred sink observes taint written 5 fields deep (default unroll).
    @Test
    fun `star deep sink any field`() = runTest<taint.StarDeepSink>()

    // Starred sanitizer must clear taint 5 fields deep (default unroll).
    @Test
    fun `star deep sanitizer clears field taint`() = runTest<taint.StarDeepSanitizer>()

    // Starred source threaded through a 5+ hop interprocedural chain that alternately hides
    // taint inside an object and exposes it. Needs the any-accessor unroll.
    @Test
    fun `star interprocedural chain`() =
        runTest<taint.StarInterproc>(unrollStrategy = TestAnalysisRunner.AnyAccessorEnabled)

    // Both ends starred: whole-object source + whole-object sink, nested object in between.
    @Test
    fun `star source and sink`() =
        runTest<taint.StarSourceAndSink>(unrollStrategy = TestAnalysisRunner.AnyAccessorEnabled)

    // Starred source + starred sanitizer over a deep field chain.
    @Test
    fun `star source and sanitizer`() =
        runTest<taint.StarSourceAndSanitizer>(unrollStrategy = TestAnalysisRunner.AnyAccessorEnabled)

    @AfterAll
    fun close() {
        closeRunner()
    }
}
