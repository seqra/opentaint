package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Pattern31Base64Test : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoConfigLoader.getConfig()?.passThrough ?: emptyList()

    @Test
    fun base64Encode001T() = assertReachable("test.base64Encode001T")

    @Test
    fun base64Encode002F() = assertNotReachable("test.base64Encode002F")
}
