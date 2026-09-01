package org.opentaint.dataflow.ap.ifds.access.tree

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Test
import java.util.concurrent.Callable
import java.util.concurrent.Executors

class AccessFactInternerTest {
    private data class Key(val value: Int) {
        override fun hashCode(): Int = 0
    }

    @Test
    fun `a collision can only replace an exact representative`() {
        val interner = AccessFactInterner<Key>(2)
        val first = interner.intern(Key(1))

        assertSame(first, interner.intern(Key(1)))
        assertEquals(Key(2), interner.intern(Key(2)))
        assertEquals(Key(1), interner.intern(Key(1)))
    }

    @Test
    fun `concurrent equal facts select one representative`() {
        val interner = AccessFactInterner<Key>(2)
        val executor = Executors.newFixedThreadPool(8)
        try {
            val results = executor.invokeAll(List(64) { Callable { interner.intern(Key(1)) } })
                .map { it.get() }

            results.forEach { assertSame(results.first(), it) }
        } finally {
            executor.shutdownNow()
        }
    }
}
