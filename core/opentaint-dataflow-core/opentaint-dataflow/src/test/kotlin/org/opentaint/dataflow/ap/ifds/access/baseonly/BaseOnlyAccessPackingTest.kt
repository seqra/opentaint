package org.opentaint.dataflow.ap.ifds.access.baseonly

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class BaseOnlyAccessPackingTest {
    private val sentinels = listOf(NO_ACCESSOR, ABSTRACT_MARK, COLLAPSED_MARK)
    private val staticReals = listOf(0, 1, 5, 100, BASE_ONLY_STATIC_MASK - BASE_ONLY_BIAS)
    private val wideReals = listOf(0, 1, 3, 7, 35, 1000, BASE_ONLY_FIELD_MASK - BASE_ONLY_BIAS)
    private val suffixReals = listOf(0, 1, 3, 7, 35, 1000, BASE_ONLY_SUFFIX_VALUE_MASK - BASE_ONLY_BIAS)

    @Test
    fun `pack then unpack round-trips every slot including sentinels and max real indices`() {
        for (s in sentinels + staticReals) {
            for (f in sentinels + wideReals) {
                for (x in sentinels + suffixReals) {
                    val packed = packBaseOnlyAccess(s, f, x)
                    assertEquals(s, packed.staticIdx, "static slot")
                    assertEquals(f, packed.fieldIdx, "field slot")
                    assertEquals(x, packed.suffixIdx, "suffix slot")
                    packed.withBaseOnlyAccessUnpacked { us, uf, ux ->
                        assertEquals(s, us, "static via withBaseOnlyAccessUnpacked")
                        assertEquals(f, uf, "field via withBaseOnlyAccessUnpacked")
                        assertEquals(x, ux, "suffix via withBaseOnlyAccessUnpacked")
                    }
                }
            }
        }
    }

    @Test
    fun `named constants decode to their triples`() {
        assertEquals(NO_ACCESSOR, EMPTY_ACCESS.staticIdx)
        assertEquals(NO_ACCESSOR, EMPTY_ACCESS.fieldIdx)
        assertEquals(NO_ACCESSOR, EMPTY_ACCESS.suffixIdx)
        assertTrue(EMPTY_ACCESS.isEmpty)

        assertEquals(NO_ACCESSOR, ABSTRACT_EMPTY_ACCESS.staticIdx)
        assertEquals(NO_ACCESSOR, ABSTRACT_EMPTY_ACCESS.fieldIdx)
        assertEquals(ABSTRACT_MARK, ABSTRACT_EMPTY_ACCESS.suffixIdx)
        assertFalse(ABSTRACT_EMPTY_ACCESS.isEmpty)
        assertTrue(ABSTRACT_EMPTY_ACCESS.hasAp)

        assertEquals(NO_ACCESSOR, FINAL_ACCESS.staticIdx)
        assertEquals(NO_ACCESSOR, FINAL_ACCESS.fieldIdx)
        assertFalse(FINAL_ACCESS.isEmpty)
        assertFalse(FINAL_ACCESS.hasAp)
    }

    @Test
    fun `pack fails fast when a slot overflows its width`() {
        assertFailsWith<IllegalArgumentException> {
            packBaseOnlyAccess(BASE_ONLY_STATIC_MASK - BASE_ONLY_BIAS + 1, NO_ACCESSOR, NO_ACCESSOR)
        }
        assertFailsWith<IllegalArgumentException> {
            packBaseOnlyAccess(NO_ACCESSOR, BASE_ONLY_FIELD_MASK - BASE_ONLY_BIAS + 1, NO_ACCESSOR)
        }
        assertFailsWith<IllegalArgumentException> {
            packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, BASE_ONLY_SUFFIX_VALUE_MASK - BASE_ONLY_BIAS + 1)
        }
    }
}
