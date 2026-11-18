package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import kotlin.test.Test
import kotlin.test.assertEquals

class AliasDirectiveTest {
    @Test
    fun `parses paths with accessors`() {
        val d = AliasDirective.parsePath("arg0.value")
        assertEquals(AccessPathBase.Argument(0), d.base)
        assertEquals(listOf(GoAliasAccessor.Field("", "value")), d.accessors)
        assertEquals(false, d.negated)
    }

    @Test
    fun `parses array and ref and negation`() {
        assertEquals(listOf(GoAliasAccessor.Array), AliasDirective.parsePath("arg1[]").accessors)
        assertEquals(listOf(GoAliasAccessor.Ref), AliasDirective.parsePath("arg0@").accessors)
        assertEquals(true, AliasDirective.parsePath("!arg1.value").negated)
    }

    @Test
    fun `parses chained accessors`() {
        val d = AliasDirective.parsePath("arg0.box.value")
        assertEquals(listOf(GoAliasAccessor.Field("", "box"), GoAliasAccessor.Field("", "value")), d.accessors)
    }

    @Test
    fun `extracts directives and depth from source`() {
        val src = """
            // depth: 1
            package util
            func F() {
                // alias: arg0, arg0.value
                aliasSink(x)
            }
        """.trimIndent()
        val parsed = AliasDirective.parseSource(src)
        assertEquals(1, parsed.depth)
        assertEquals(1, parsed.expectations.size)
        assertEquals(2, parsed.expectations[0].paths.size)
        assertEquals(false, parsed.expectations[0].engineOnly)
    }

    @Test
    fun `extracts engine only directives`() {
        val src = """
            package util
            func F() {
                // engine alias: arg0.inner.a, !arg1
                aliasSink(x)
            }
        """.trimIndent()
        val expectation = AliasDirective.parseSource(src).expectations.single()
        assertEquals(true, expectation.engineOnly)
        assertEquals(2, expectation.paths.size)
        assertEquals(true, expectation.paths[1].negated)
    }
}
