package org.opentaint.dataflow.ap.ifds.access.baseonly

import kotlin.test.Test
import kotlin.test.assertEquals

class BaseOnlySummaryNormalizationTest {
    @Test
    fun `field initial is moved to suffix when summary final has suffix`() {
        val static = 41
        val field = 73
        val initial = packBaseOnlyAccess(static, ABSTRACT_MARK, NO_ACCESSOR)
        val final = packBaseOnlyAccess(static, field, ABSTRACT_MARK)

        val normalized = normalizeSummaryInitialAccess(initial, final)

        assertEquals(packBaseOnlyAccess(static, NO_ACCESSOR, ABSTRACT_MARK), normalized)
    }

    @Test
    fun `field initial is unchanged when summary final has field abstraction`() {
        val initial = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)
        val final = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)

        assertEquals(initial, normalizeSummaryInitialAccess(initial, final))
    }

    @Test
    fun `suffix initial is unchanged`() {
        val initial = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
        val final = packBaseOnlyAccess(NO_ACCESSOR, 73, ABSTRACT_MARK)

        assertEquals(initial, normalizeSummaryInitialAccess(initial, final))
    }
}
