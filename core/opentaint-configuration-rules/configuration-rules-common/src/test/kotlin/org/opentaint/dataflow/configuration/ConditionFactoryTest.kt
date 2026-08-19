package org.opentaint.dataflow.configuration

import kotlin.test.Test
import kotlin.test.assertSame

class ConditionFactoryTest {
    @Test
    fun `false condition is shared`() {
        val first: Any = mkFalse<String>()
        val second: Any = mkFalse<Int>()

        assertSame(first, second)
    }
}
