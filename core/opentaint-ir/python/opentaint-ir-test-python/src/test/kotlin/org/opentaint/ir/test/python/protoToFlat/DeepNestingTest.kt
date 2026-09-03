package org.opentaint.ir.test.python.protoToFlat

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class DeepNestingTest : RawFlatModuleTestBase() {

    @Test
    fun `deeply nested binary expression exceeds the default protobuf recursion limit`() {
        val terms = 300
        val source = "def total():\n    return " + (1..terms).joinToString(" + ") { "$it" } + "\n"

        val module = lowerSourceToFlat(source)

        assertEquals(1, module.functions.count { it.qualifiedName.endsWith(".total") })
    }
}
