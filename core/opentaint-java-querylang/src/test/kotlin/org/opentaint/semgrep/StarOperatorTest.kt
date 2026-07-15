package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle.PER_CLASS
import org.opentaint.semgrep.util.SampleBasedTest
import kotlin.test.Test

@TestInstance(PER_CLASS)
class StarOperatorTest : SampleBasedTest() {
    @Test
    fun `star source field flow`() = runTest<taint.StarSource>()

    @Test
    fun `star sink any field`() = runTest<taint.StarSink>()

    @Test
    fun `star sanitizer clears field taint`() = runTest<taint.StarSanitizer>()

    @AfterAll
    fun close() {
        closeRunner()
    }
}
