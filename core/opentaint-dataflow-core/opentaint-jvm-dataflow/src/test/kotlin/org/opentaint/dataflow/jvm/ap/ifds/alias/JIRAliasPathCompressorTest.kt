package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase.Companion.Argument
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import kotlin.test.Test
import kotlin.test.assertEquals

class JIRAliasPathCompressorTest {
    @Test
    fun `drops permutation facts and preserves unaffected facts`() {
        val shortA = alias(a, exit)
        val shortB = alias(b, exit)
        val aliases = listOf(
            shortA,
            shortB,
            alias(a, b, a, exit),
            alias(b, a, b, exit),
        )

        val compressed = JIRAliasPathCompressor.compress(aliases)

        assertEquals(setOf(shortA, shortB), compressed.toSet())
    }

    @Test
    fun `drops permutation facts instead of shortening them`() {
        val aliases = listOf(
            alias(a, b, a, exit),
            alias(b, a, b, exit),
        )

        assertEquals(emptyList(), JIRAliasPathCompressor.compress(aliases))
    }

    @Test
    fun `does not compress acyclic accessor chains`() {
        val aliases = listOf(
            alias(a, b, exit),
            alias(b, exit),
        )

        assertEquals(aliases, JIRAliasPathCompressor.compress(aliases))
    }

    @Test
    fun `does not compress single accessor self loop`() {
        val aliases = listOf(alias(a, a, a, exit))

        assertEquals(aliases, JIRAliasPathCompressor.compress(aliases))
    }

    private fun alias(vararg accessors: AliasAccessor): AliasApInfo =
        AliasApInfo(Argument(0), accessors.toList())

    private companion object {
        val a = field("a")
        val b = field("b")
        val exit = field("exit")

        fun field(name: String) = AliasAccessor.Field("Test", name, "java.lang.Object")
    }
}
