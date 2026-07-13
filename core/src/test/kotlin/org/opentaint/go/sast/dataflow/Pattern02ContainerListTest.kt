package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoDefaultConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Pattern02ContainerListTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoDefaultConfigLoader.loadConfig()?.passThrough ?: emptyList()

    @Test fun containerListPushFront001T() = assertReachable("test.containerListPushFront001T")
    @Test fun containerListPushFront002F() = assertNotReachable("test.containerListPushFront002F")
}
