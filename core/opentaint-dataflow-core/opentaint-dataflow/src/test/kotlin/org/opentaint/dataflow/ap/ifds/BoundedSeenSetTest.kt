package org.opentaint.dataflow.ap.ifds

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.util.concurrent.Callable
import java.util.concurrent.Executors

class BoundedSeenSetTest {
    private data class Key(val value: Int) {
        override fun hashCode(): Int = 0
    }

    @Test
    fun `an exact retained repeat is rejected`() {
        val seen = BoundedSeenSet<Key>(4, 4)

        assertTrue(seen.markNew(Key(1)))
        assertFalse(seen.markNew(Key(1)))
    }

    @Test
    fun `collisions retain exact values until the bound`() {
        val seen = BoundedSeenSet<Key>(4, 4)

        assertTrue(seen.markNew(Key(1)))
        assertTrue(seen.markNew(Key(2)))
        assertTrue(seen.markNew(Key(3)))
        assertFalse(seen.markNew(Key(1)))
        assertFalse(seen.markNew(Key(2)))
        assertFalse(seen.markNew(Key(3)))
    }

    @Test
    fun `a distinct value is admitted after the retention bound`() {
        val seen = BoundedSeenSet<Key>(4, 4)
        (1..3).forEach { assertTrue(seen.markNew(Key(it))) }

        assertTrue(seen.markNew(Key(4)))
        assertTrue(seen.markNew(Key(4)))
    }

    @Test
    fun `growth preserves retained values`() {
        val seen = BoundedSeenSet<Key>(8, 2)
        (1..6).forEach { assertTrue(seen.markNew(Key(it))) }

        (1..6).forEach { assertFalse(seen.markNew(Key(it))) }
    }

    @Test
    fun `concurrent exact repeats admit one value`() {
        val seen = BoundedSeenSet<Key>(4, 4)
        val executor = Executors.newFixedThreadPool(8)
        try {
            val admitted = executor.invokeAll(List(64) { Callable { seen.markNew(Key(1)) } })
                .count { it.get() }

            assertEquals(1, admitted)
        } finally {
            executor.shutdownNow()
        }
    }
}
