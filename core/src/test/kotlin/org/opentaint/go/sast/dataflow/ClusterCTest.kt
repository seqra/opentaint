package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ClusterCTest : AnalysisTest() {

    @Test fun closureCaptureReturn001T() = assertReachable("test.closureCaptureReturn001T")
    @Test fun closureCaptureReturn002F() = assertNotReachable("test.closureCaptureReturn002F")

    // not an FN: nested-struct constructor return already handled (taint propagates
    // through NewCtorOuter to o.inner.v) — passes, so left enabled.
    @Test fun nestedStructConstructor001T() = assertReachable("test.nestedStructConstructor001T")
    @Test fun nestedStructConstructor002F() = assertNotReachable("test.nestedStructConstructor002F")

    // not an FN: concrete-receiver multi-method dispatch already handled.
    @Test fun interfaceLaunderingConcrete001T() = assertReachable("test.interfaceLaunderingConcrete001T")
    // not an FN: interface-variable multi-implementor dispatch already handled.
    @Test fun interfaceLaunderingIface001T() = assertReachable("test.interfaceLaunderingIface001T")
    @Test fun interfaceLaundering002F() = assertNotReachable("test.interfaceLaundering002F")
}
