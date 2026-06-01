package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Pattern01StringsBuilderTest : AnalysisTest() {

    // Opt into bundled go-config: by default AnalysisTest disables it.
    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    @Test fun stringsBuilderWrite001T() = assertReachable("test.stringsBuilderWrite001T")
    @Test fun stringsBuilderWrite002F() = assertNotReachable("test.stringsBuilderWrite002F")
}
