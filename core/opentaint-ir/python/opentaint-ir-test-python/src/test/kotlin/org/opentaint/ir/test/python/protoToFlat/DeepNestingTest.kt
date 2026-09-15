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

    @Test
    fun `deeply nested statements exceed the default protobuf recursion limit`() {
        val depth = 90
        val body = StringBuilder("def nested(x):\n")
        for (level in 1..depth) {
            body.append("    ".repeat(level)).append("if x > $level:\n")
        }
        body.append("    ".repeat(depth + 1)).append("return $depth\n")
        body.append("    return 0\n")

        val module = lowerSourceToFlat(body.toString())

        assertEquals(1, module.functions.count { it.qualifiedName.endsWith(".nested") })
    }
}
