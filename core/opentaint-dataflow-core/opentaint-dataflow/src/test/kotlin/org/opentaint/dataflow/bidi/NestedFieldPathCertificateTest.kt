package org.opentaint.dataflow.bidi

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull

class NestedFieldPathCertificateTest {
    @Test fun `suffix follows the complete recursive word`() {
        val f = 1
        val g = 2
        val h = 3
        val nested = listOf(
            NestedFieldPathCertificate.Rule(0, emptyList(), null),
            NestedFieldPathCertificate.Rule(0, listOf(g), 0, listOf(f)),
        )
        val observer = RegularFieldPathQuery.compile(1, RegularFieldPathQuery.grammar(listOf(g, f, h), emptyList()))!!
        assertEquals(false, NestedFieldPathCertificate.disjoint(nested, 1, observer, listOf(h), completeSlice = true))
        assertEquals(true, NestedFieldPathCertificate.disjoint(nested, 1, observer, emptyList(), completeSlice = true))
        assertNull(NestedFieldPathCertificate.disjoint(nested, 1, observer, emptyList(), completeSlice = false))
    }

    @Test fun `mutual recursion carries the paired state across both owners`() {
        val f = 1
        val g = 2
        val h = 3
        val nested = listOf(
            NestedFieldPathCertificate.Rule(0, listOf(g), 1, listOf(f)),
            NestedFieldPathCertificate.Rule(1, listOf(h), null),
            NestedFieldPathCertificate.Rule(1, listOf(g), 0, listOf(f)),
        )
        fun accepts(word: List<Int>) =
            RegularFieldPathQuery.compile(1, RegularFieldPathQuery.grammar(word, emptyList()))!!
        assertEquals(false, NestedFieldPathCertificate.disjoint(nested, 2, accepts(listOf(g,g,g,h,f,f,f)),
            emptyList(), completeSlice = true))
        assertEquals(true, NestedFieldPathCertificate.disjoint(nested, 2, accepts(listOf(g,g,h,f,f)),
            emptyList(), completeSlice = true))
    }
}
