package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class OverloadedFunctionsTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        val SOURCE = """
from typing import overload

@overload
def unwrap(obj: int) -> int: ...

@overload
def unwrap(obj: str) -> str: ...

def unwrap(obj):
    if isinstance(obj, int):
        return obj + 1
    return obj

class Box:
    @overload
    def get(self, key: int) -> int: ...

    @overload
    def get(self, key: str) -> str: ...

    def get(self, key):
        return self.values[key]

    @property
    def size(self) -> int:
        return self._size

    @size.setter
    def size(self, value: int) -> None:
        self._size = value
        """.trimIndent()
    }

    @BeforeAll fun setup() { cp = buildFromSource(SOURCE) }

    private val module get() = cp.findModuleOrNull("__test__")!!

    @Test fun `overload group collapses to a single function`() {
        val unwrap = module.functions.filter { it.name == "unwrap" }
        assertEquals(1, unwrap.size,
            "Expected only the implementation, got: ${unwrap.map { it.qualifiedName }}")
    }

    @Test fun `overload implementation body is kept`() {
        val f = cp.findFunctionOrNull("__test__.unwrap")!!
        assertTrue(f.instList.any { it is PIRCall },
            "Expected the implementation body (isinstance call), got: ${f.instList.map { it::class.simpleName }}")
        assertTrue(f.instList.size > 1,
            "Overload stub body would be a single expression; got ${f.instList.size} instructions")
    }

    @Test fun `overloaded method collapses to a single method`() {
        val box = cp.findClassOrNull("__test__.Box")!!
        val get = box.methods.filter { it.name == "get" }
        assertEquals(1, get.size,
            "Expected only the implementation, got: ${get.map { it.qualifiedName }}")
    }

    @Test fun `property getter and setter both survive`() {
        val box = cp.findClassOrNull("__test__.Box")!!
        val size = box.properties.single { it.name == "size" }
        assertNotNull(size.getter, "property getter should be present")
        assertNotNull(size.setter, "property setter should be present")
    }
}
