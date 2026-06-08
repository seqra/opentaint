package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Pattern03SyncAtomicTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    // Pattern 3: PASSES — atomic.Value rules in bundled config already model Store/Load correctly.
    @Test fun atomicValueLoad001T() = assertReachable("test.atomicValueLoad001T")
    @Test fun atomicValueLoad002F() = assertNotReachable("test.atomicValueLoad002F")
}
