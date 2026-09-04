package org.opentaint.ir.test.python.tier2

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Tag
import org.opentaint.ir.api.python.*
import org.opentaint.ir.test.python.PIRTestBase

@Tag("tier2")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ConstructorReturnSelfTest : PIRTestBase() {

    private lateinit var cp: PIRClasspath

    companion object {
        val SOURCE = """
class Implicit:
    def __init__(self, x: int):
        self.x = x

class EarlyReturn:
    def __init__(self, x: int):
        if x < 0:
            return
        self.x = x

class RenamedSelf:
    def __init__(this, x: int):
        this.x = x

class NoParams:
    def __init__():
        pass

class Regular:
    def method(self):
        return
        """.trimIndent()
    }

    @BeforeAll fun setup() { cp = buildFromSource(SOURCE) }

    private fun init(className: String): PIRFunction =
        cp.findClassOrNull("__test__.$className")!!.methods.first { it.name == "__init__" }

    private fun assertEveryReturnIsSelf(fn: PIRFunction) {
        val self = fn.parameters.first().name
        val returns = fn.instList.filterIsInstance<PIRReturn>()
        Assertions.assertTrue(returns.isNotEmpty(), "Expected at least one PIRReturn in ${fn.qualifiedName}")
        returns.forEach { ret ->
            val value = ret.value
            Assertions.assertTrue(
                value is PIRLocal && value.name == self,
                "Expected `return $self` in ${fn.qualifiedName}, got `return $value`",
            )
        }
    }

    @Test
    fun `implicit return exits with return self`() = assertEveryReturnIsSelf(init("Implicit"))

    @Test
    fun `early bare return becomes return self`() = assertEveryReturnIsSelf(init("EarlyReturn"))

    @Test
    fun `return self uses the first parameter name`() = assertEveryReturnIsSelf(init("RenamedSelf"))

    @Test
    fun `parameter-less __init__ falls back to value-less return`() {
        val fn = init("NoParams")
        val returns = fn.instList.filterIsInstance<PIRReturn>()
        Assertions.assertTrue(returns.isNotEmpty(), "Expected a PIRReturn in ${fn.qualifiedName}")
        Assertions.assertTrue(
            returns.all { it.value == null },
            "A parameter-less __init__ must fall back to a value-less return",
        )
    }

    @Test
    fun `non-constructor bare return stays value-less`() {
        val method = cp.findClassOrNull("__test__.Regular")!!.methods.first { it.name == "method" }
        val returns = method.instList.filterIsInstance<PIRReturn>()
        Assertions.assertTrue(returns.isNotEmpty(), "Expected a PIRReturn")
        Assertions.assertTrue(
            returns.all { it.value == null },
            "A regular method's bare `return` must stay value-less",
        )
    }
}
