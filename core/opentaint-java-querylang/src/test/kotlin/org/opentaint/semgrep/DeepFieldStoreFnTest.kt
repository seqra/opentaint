package org.opentaint.semgrep

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle.PER_CLASS
import org.opentaint.semgrep.util.SampleBasedTest
import kotlin.test.Test

@TestInstance(PER_CLASS)
class DeepFieldStoreFnTest : SampleBasedTest() {
    @Test
    fun `deep field store FN`() = runTest<taint.DeepFieldStoreFn>()

    @AfterAll
    fun close() {
        closeRunner()
    }
}
