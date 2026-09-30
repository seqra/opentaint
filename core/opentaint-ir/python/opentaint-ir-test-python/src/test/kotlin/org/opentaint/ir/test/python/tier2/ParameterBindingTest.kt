package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRLocalVar
import org.opentaint.ir.api.python.PIRParameterRef
import org.opentaint.ir.api.python.PIRStoreAttr
import org.opentaint.ir.api.python.operands
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ParameterBindingTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        val SOURCE = """
def read_only(p, q):
    return p + q

def assigned(p):
    p = 1
    return p

def augmented(p):
    p += 1
    return p

def loop_target(p, xs):
    for p in xs:
        pass
    return p

def except_target(p):
    try:
        pass
    except Exception as p:
        pass

def with_target(p, cm):
    with cm as p:
        pass

def walrus_target(p):
    if (p := 1):
        pass

def deleted(p):
    del p

def captured(p):
    def inner():
        return p
    return inner
        """.trimIndent()
    }

    @BeforeAll fun setup() { cp = buildFromSource(SOURCE) }

    private fun function(name: String): PIRFunction = cp.findFunctionOrNull("__test__.$name")!!

    private fun PIRFunction.values() = instList.flatMap { it.operands }

    private fun isParameterCopy(inst: PIRInstruction, name: String) =
        inst is PIRAssign && inst.target.name == name && (inst.expr as? PIRParameterRef)?.name == name

    private fun assertReadDirectly(fn: PIRFunction, name: String) {
        Assertions.assertTrue(
            fn.values().none { it is PIRLocalVar && it.name == name },
            "Expected no local for parameter `$name` in ${fn.qualifiedName}: ${fn.instList}",
        )
        Assertions.assertTrue(
            fn.values().any { it is PIRParameterRef && it.name == name },
            "Expected `$name` to be read as a parameter in ${fn.qualifiedName}: ${fn.instList}",
        )
    }

    private fun assertCopied(fn: PIRFunction, name: String) {
        Assertions.assertTrue(
            isParameterCopy(fn.cfg.entry, name),
            "Expected `$name = param $name` as the entry instruction of ${fn.qualifiedName}: ${fn.instList}",
        )
    }

    @Test
    fun `read-only parameters are read directly`() {
        val fn = function("read_only")
        assertReadDirectly(fn, "p")
        assertReadDirectly(fn, "q")
    }

    @Test
    fun `assigned parameter is copied`() = assertCopied(function("assigned"), "p")

    @Test
    fun `augmented parameter is copied`() = assertCopied(function("augmented"), "p")

    @Test
    fun `loop-target parameter is copied`() = assertCopied(function("loop_target"), "p")

    @Test
    fun `except-target parameter is copied`() = assertCopied(function("except_target"), "p")

    @Test
    fun `with-target parameter is copied`() = assertCopied(function("with_target"), "p")

    @Test
    fun `walrus-target parameter is copied`() = assertCopied(function("walrus_target"), "p")

    @Test
    fun `deleted parameter is copied`() = assertCopied(function("deleted"), "p")

    @Test
    fun `only rebound parameters are copied`() {
        val fn = function("loop_target")
        assertReadDirectly(fn, "xs")
    }

    @Test
    fun `captured parameter seeds its cell from the parameter`() {
        val fn = function("captured")
        assertReadDirectly(fn, "p")
        Assertions.assertTrue(
            fn.instList.any { it is PIRStoreAttr && (it.value as? PIRParameterRef)?.name == "p" },
            "Expected the cell of `p` to be seeded from the parameter: ${fn.instList}",
        )
    }
}
