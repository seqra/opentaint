package org.opentaint.jvm.sast.dataflow.rules

import kotlin.test.Test
import kotlin.test.assertNotSame
import kotlin.test.assertSame

class ResolvedValueInternerTest {
    private data class Value(val id: Int)

    @Test
    fun `equal resolved values share one representative`() {
        val interner = ResolvedValueInterner<Value>()
        val first = interner.intern(Value(1))
        val second = interner.intern(Value(1))

        assertSame(first, second)
    }

    @Test
    fun `different resolved values remain distinct`() {
        val interner = ResolvedValueInterner<Value>()
        val first = interner.intern(Value(1))
        val second = interner.intern(Value(2))

        assertNotSame(first, second)
    }
}
