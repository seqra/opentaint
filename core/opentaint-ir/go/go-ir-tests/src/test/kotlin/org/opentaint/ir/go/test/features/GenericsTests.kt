package org.opentaint.ir.go.test.features

import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.extension.ExtendWith
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.ext.findFunctionByFullName
import org.opentaint.ir.go.ext.findFunctionByName
import org.opentaint.ir.go.ext.findNamedTypeByName
import org.opentaint.ir.go.test.GoIRSanityChecker
import org.opentaint.ir.go.test.GoIRTestBuilder
import org.opentaint.ir.go.test.GoIRTestExtension
import java.nio.file.Files

/**
 * Tests for Go generics (type parameters, constraints, instantiation).
 */
@ExtendWith(GoIRTestExtension::class)
class GenericsTests {

    @Test
    fun `generic function with type parameter`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            func Identity[T any](x T) T { return x }
            func use() int { return Identity(42) }
        """.trimIndent())

        // With instantiateGenerics=true, we should see instantiated versions
        val allFns = prog.allFunctions()
        // Should have at least the instantiated Identity[int]
        assertThat(allFns).isNotEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `generic struct type`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            type Pair[A, B any] struct { First A; Second B }
            func use() Pair[int, string] {
                return Pair[int, string]{First: 1, Second: "hello"}
            }
        """.trimIndent())

        // Should find the Pair type
        val allTypes = prog.allNamedTypes()
        val pairTypes = allTypes.filter { it.name.startsWith("Pair") }
        assertThat(pairTypes).isNotEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `generic function with comparable constraint`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            func Contains[T comparable](slice []T, target T) bool {
                for _, v := range slice {
                    if v == target { return true }
                }
                return false
            }
            func use() bool {
                return Contains([]int{1, 2, 3}, 2)
            }
        """.trimIndent())

        val allFns = prog.allFunctions()
        assertThat(allFns).isNotEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `generic interface constraint`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            type Number interface { ~int | ~float64 }
            func Sum[T Number](xs []T) T {
                var total T
                for _, x := range xs {
                    total += x
                }
                return total
            }
            func use() int { return Sum([]int{1, 2, 3}) }
        """.trimIndent())

        val allFns = prog.allFunctions()
        assertThat(allFns).isNotEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `generic method on type`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            type Stack[T any] struct { items []T }
            func (s *Stack[T]) Push(v T) { s.items = append(s.items, v) }
            func (s *Stack[T]) Len() int { return len(s.items) }
            func use() int {
                s := &Stack[int]{}
                s.Push(1)
                return s.Len()
            }
        """.trimIndent())

        val allFns = prog.allFunctions()
        assertThat(allFns).isNotEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `methods of a generic type have bodies and belong to the type`(builder: GoIRTestBuilder) {
        val prog = builder.buildFromSource("""
            package p
            type Box[T any] struct { v T }
            func (b Box[T]) Get() T { return b.v }
            func (b *Box[T]) Set(v T) { b.v = v }
            func (b Box[T]) Unused() T { return b.v }
            func use() int {
                b := &Box[int]{}
                b.Set(1)
                return b.Get()
            }
        """.trimIndent())

        val box = prog.findNamedTypeByName("Box")!!
        assertThat(box.methods.map { it.name }).contains("Get", "Unused")
        assertThat(box.pointerMethods.map { it.name }).contains("Set")
        for (name in listOf("(test/p.Box[T]).Get", "(*test/p.Box[T]).Set", "(test/p.Box[T]).Unused")) {
            assertThat(prog.findFunctionByFullName(name)?.bodyAvailable).describedAs(name).isTrue()
        }
        assertThat(declaredWithoutBody(prog)).isEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    @Test
    fun `methods with their own type parameters have bodies`(builder: GoIRTestBuilder) {
        val root = Files.createTempDirectory("goir-generic-methods")
        root.resolve("go.mod").toFile().writeText("module test/p\ngo 1.27.0\n")
        root.resolve("p.go").toFile().writeText("""
            package p
            type Conv struct{}
            func (Conv) Pass[T any](v T) T { return v }
            func (Conv) Unused[T any](v T) T { return v }
            func use() string { return Conv{}.Pass("x") }
        """.trimIndent())

        val prog = builder.buildFromDir(root, GoIRLoadConfig())

        for (name in listOf("(test/p.Conv).Pass", "(test/p.Conv).Unused")) {
            assertThat(prog.findFunctionByFullName(name)?.bodyAvailable).describedAs(name).isTrue()
        }
        assertThat(declaredWithoutBody(prog)).isEmpty()

        GoIRSanityChecker.check(prog).assertNoErrors()
    }

    /** The project functions that declare a body the program doesn't carry. */
    private fun declaredWithoutBody(prog: GoIRProgram): List<String> =
        prog.allFunctions()
            .filter { it.pkg?.isProject == true && it.hasBody && !it.bodyAvailable }
            .map { it.fullName }
}
