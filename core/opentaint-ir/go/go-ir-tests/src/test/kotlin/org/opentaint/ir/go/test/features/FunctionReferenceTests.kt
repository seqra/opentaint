package org.opentaint.ir.go.test.features

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.extension.ExtendWith
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.reference
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.ext.findExpressions
import org.opentaint.ir.go.test.GoIRTestBuilder
import org.opentaint.ir.go.test.GoIRTestExtension

/**
 * Tests for the resolution of function references.
 */
@ExtendWith(GoIRTestExtension::class)
class FunctionReferenceTests {
    private val twinMethods = """
        package p
        type A struct{}
        type B struct{}
        func (A) run(s string) string {
            f := func() string { return s }
            return f()
        }
        func (B) run(s string) string {
            f := func() string { return s + "!" }
            return f()
        }
    """.trimIndent()

    private fun fullNames(functions: List<GoIRFunction>) = functions.map { it.fullName }

    @Test
    fun `reference of a closure resolves to the closure`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource(twinMethods)

        val closures = prog.allFunctions().filter { it.name == "run$1" }
        assertThat(fullNames(closures)).containsExactlyInAnyOrder("(test/p.A).run$1", "(test/p.B).run$1")

        val resolved = closures.map { closure ->
            closure.reference().also { it.program = prog }.function
        }
        assertThat(fullNames(resolved)).isEqualTo(fullNames(closures))
    }

    @Test
    fun `anonymous functions of a method are its own closures`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource(twinMethods)

        for (receiver in listOf("A", "B")) {
            val method = prog.allFunctions().single { it.fullName == "(test/p.$receiver).run" }
            assertThat(fullNames(method.anonymousFunctions.map { it.function }))
                .containsExactly("(test/p.$receiver).run$1")
        }
    }

    @Test
    fun `MakeClosure in a method creates the closure of this method`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource(twinMethods)

        for (receiver in listOf("A", "B")) {
            val method = prog.allFunctions().single { it.fullName == "(test/p.$receiver).run" }
            val created = method.findExpressions<GoIRMakeClosureExpr>().map { it.fn }
            assertThat(fullNames(created)).containsExactly("(test/p.$receiver).run$1")
        }
    }
}
