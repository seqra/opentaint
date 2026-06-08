package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class MapOpsTest : AnalysisTest() {

    // Map literal with struct values: needs field-sensitive map element composition
    @Test fun mapStruct001T() = assertReachable("test.mapStruct001T")
    @Test fun mapStruct002F() = assertNotReachable("test.mapStruct002F")

    // Map range iteration: GoIRRangeExpr → GoIRNextExpr → GoIRExtractExpr
    @Test fun mapIter001T() = assertReachable("test.mapIter001T")
    @Test fun mapIter002F() = assertNotReachable("test.mapIter002F")

    @Test fun mapKeyTaint001T() = assertReachable("test.mapKeyTaint001T")

    @Test fun mapDelete001T() = assertReachable("test.mapDelete001T")

    // Map comma-ok lookup produces tuple via GoIRExtractExpr
    @Test fun mapCommaOk001T() = assertReachable("test.mapCommaOk001T")
    @Test fun mapCommaOk002F() = assertNotReachable("test.mapCommaOk002F")
}
