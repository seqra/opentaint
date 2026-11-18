package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import kotlin.test.Test

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class StructLiteralTest : AnalysisTest() {
    // Literal assigned to a new variable
    @Test fun structLit001T() = assertReachable("test.structLit001T")
    @Test fun structLit002F() = assertNotReachable("test.structLit002F")
    @Test fun structLitUnkeyed001T() = assertReachable("test.structLitUnkeyed001T")
    @Test fun structLitUnkeyed002F() = assertNotReachable("test.structLitUnkeyed002F")
    @Test fun structLitPointer001T() = assertReachable("test.structLitPointer001T")
    @Test fun structLitPointer002F() = assertNotReachable("test.structLitPointer002F")

    // Literal assigned over an existing value
    @Test fun structLitReassign001T() = assertReachable("test.structLitReassign001T")
    @Test fun structLitReassign002F() = assertNotReachable("test.structLitReassign002F")
    @Test fun structLitReassign003F() = assertNotReachable("test.structLitReassign003F")
    @Test fun structLitThroughPointer001T() = assertReachable("test.structLitThroughPointer001T")
    @Test fun structLitThroughPointer002F() = assertNotReachable("test.structLitThroughPointer002F")
    @Test fun structLitThroughPointer003F() = assertNotReachable("test.structLitThroughPointer003F")
    @Test fun structLitAddressTaken001T() = assertReachable("test.structLitAddressTaken001T")
    @Test fun structLitAddressTaken002F() = assertNotReachable("test.structLitAddressTaken002F")
    @Test fun structLitInLoop001T() = assertReachable("test.structLitInLoop001T")
    @Test fun structLitInBranch001T() = assertReachable("test.structLitInBranch001T")

    // Literal stored into a field, an element or a nested literal
    @Test fun structLitToField001T() = assertReachable("test.structLitToField001T")
    @Test fun structLitToField002F() = assertNotReachable("test.structLitToField002F")
    @Test fun structLitNested001T() = assertReachable("test.structLitNested001T")
    @Test fun structLitNested002F() = assertNotReachable("test.structLitNested002F")
    @Test fun structLitNested003F() = assertNotReachable("test.structLitNested003F")
    @Test fun structLitInSlice001T() = assertReachable("test.structLitInSlice001T")
    @Test fun structLitInSlice002F() = assertNotReachable("test.structLitInSlice002F")
    @Test fun structLitInArray001T() = assertReachable("test.structLitInArray001T")
    @Test fun structLitInMap001T() = assertReachable("test.structLitInMap001T")
    @Test fun structLitPointerElements001T() = assertReachable("test.structLitPointerElements001T")

    // Literal used as a value
    @Test fun structLitAsArgument001T() = assertReachable("test.structLitAsArgument001T")
    @Test fun structLitAsArgument002F() = assertNotReachable("test.structLitAsArgument002F")
    @Test fun structLitAsReceiver001T() = assertReachable("test.structLitAsReceiver001T")
    @Test fun structLitInInterface001T() = assertReachable("test.structLitInInterface001T")
    @Test fun structLitCaptured001T() = assertReachable("test.structLitCaptured001T")

    // Empty literals
    @Test fun structLitEmpty001F() = assertNotReachable("test.structLitEmpty001F")
    @Test fun arrayLitEmpty001F() = assertNotReachable("test.arrayLitEmpty001F")
    @Test fun arrayLitEmpty002T() = assertReachable("test.arrayLitEmpty002T")
}
