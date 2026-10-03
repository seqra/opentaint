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

        val compressed = compress(aliases)

        assertEquals(setOf(shortA, shortB), compressed.toSet())
    }

    @Test
    fun `drops permutation facts instead of shortening them`() {
        val aliases = listOf(
            alias(a, b, a, exit),
            alias(b, a, b, exit),
        )

        assertEquals(emptyList(), compress(aliases))
    }

    @Test
    fun `does not compress acyclic accessor chains`() {
        val aliases = listOf(
            alias(a, b, exit),
            alias(b, exit),
        )

        assertEquals(aliases, compress(aliases))
    }

    @Test
    fun `drops paths continuing past unbounded accessors`() {
        val element = AliasAccessor.Field("java.lang.Iterable", "Element", "java.lang.Object")
        val collection = AliasAccessor.Field("Test", "collection", "java.lang.Iterable")
        val aliases = listOf(
            alias(element),
            alias(element, exit),
            alias(collection, element),
            alias(AliasAccessor.Array),
            alias(AliasAccessor.Array, exit),
        )

        assertEquals(
            listOf(alias(element), alias(AliasAccessor.Array)),
            compress(aliases),
        )
    }

    @Test
    fun `keeps typed field to array access`() {
        val arrayField = AliasAccessor.Field("Test", "values", "Test[]")
        val alias = alias(arrayField, AliasAccessor.Array)

        assertEquals(listOf(alias), compress(listOf(alias)))
    }

    @Test
    fun `keeps repeated accessor facts without a field permutation`() {
        val short = alias(a, exit)
        val aliases = listOf(short, alias(a, a, a, exit))

        assertEquals(aliases, compress(aliases))
    }

    private fun compress(aliases: List<AliasApInfo>) =
        JIRAliasPathCompressor.compress(aliases)

    private fun alias(vararg accessors: AliasAccessor): AliasApInfo =
        AliasApInfo(Argument(0), accessors.toList())

    private companion object {
        val a = field("a")
        val b = field("b")
        val exit = field("exit")

        fun field(name: String) = AliasAccessor.Field("Test", name, "Test")
    }
}
