package org.opentaint.semgrep

import org.opentaint.semgrep.util.SampleBasedTest
import kotlin.test.Test

class DeepFieldStoreFnTest : SampleBasedTest() {
    @Test
    fun `deep field store FN`() = runTest<taint.DeepFieldStoreFn>()
}
