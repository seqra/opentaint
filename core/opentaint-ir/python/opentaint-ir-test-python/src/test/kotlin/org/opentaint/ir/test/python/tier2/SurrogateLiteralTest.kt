package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Tag
import org.opentaint.ir.api.python.*
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SurrogateLiteralTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        val SOURCE = """
            import re

            SURROGATE_REGEX = re.compile("([\ud800-\udfff])")

            def strip(s):
                return SURROGATE_REGEX.sub("", s)
        """
    }

    @BeforeAll fun setup() { cp = buildFromSource(SOURCE) }

    private val module get() = cp.findModuleOrNull("__test__")!!

    @Test fun `lone surrogate literal does not drop the enclosing definition`() {
        assertTrue(module.fields.any { it.name == "SURROGATE_REGEX" },
            "module-level constant must survive: got ${module.fields.map { it.name }}")
    }

    @Test fun `surrogate literal produces no diagnostics`() {
        assertEquals(emptyList<String>(), module.diagnostics.map { it.message })
    }

    @Test fun `code using the constant is still lowered`() {
        assertNotNull(cp.findFunctionOrNull("__test__.strip"))
    }
}
