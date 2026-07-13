package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule.PassThrough
import org.opentaint.go.config.GoDefaultConfigLoader
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class PatternUrlQueryUnescapeTest : AnalysisTest() {

    override val commonPassRules: List<PassThrough> =
        GoDefaultConfigLoader.loadConfig()?.passThrough ?: emptyList()

    @Test fun queryUnescapeMultiRet001T() = assertReachable("test.queryUnescapeMultiRet001T")

    @Test fun queryUnescapeMultiRet002F() = assertNotReachable("test.queryUnescapeMultiRet002F")

    @Test fun queryUnescapeReassign001T() = assertReachable("test.queryUnescapeReassign001T")
}
