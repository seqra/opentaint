package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoDefaultConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Pattern19AppendResliceTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoDefaultConfigLoader.loadConfig()?.passThrough ?: emptyList()

    @Test fun appendReslice001T() = assertReachable("test.appendReslice001T")
    @Test fun appendReslice002F() = assertNotReachable("test.appendReslice002F")

    @Test fun appendResliceInterproc001T() = assertReachable("test.appendResliceInterproc001T")
}
