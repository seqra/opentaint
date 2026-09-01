package org.opentaint.dataflow.jvm.ap.ifds

import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class DirectMappedExactCacheTest {
    private data class Key(val value: Int) {
        override fun hashCode(): Int = 0
    }

    @Test
    fun `hit returns the exact stored result`() {
        val cache = DirectMappedExactCache<Key, String>(2)

        assertEquals("value-1", cache.getOrCompute(Key(1)) { "value-${it.value}" })
        assertEquals("value-1", cache.getOrCompute(Key(1)) { "different" })
        assertEquals(2, cache.slotCount())
    }

    @Test
    fun `collision recomputes the exact result`() {
        val cache = DirectMappedExactCache<Key, String>(2)

        cache.getOrCompute(Key(1)) { "value-${it.value}" }
        assertEquals("value-2", cache.getOrCompute(Key(2)) { "value-${it.value}" })
        assertEquals("value-1", cache.getOrCompute(Key(1)) { "value-${it.value}" })
    }

    @Test
    fun `concurrent collisions return exact results`() {
        val cache = DirectMappedExactCache<Key, String>(2)
        val correct = AtomicBoolean(true)
        val executor = Executors.newFixedThreadPool(8)

        repeat(8) { worker ->
            executor.submit {
                repeat(100_000) { iteration ->
                    val key = Key((iteration + worker) and 31)
                    val result = cache.getOrCompute(key) { "value-${it.value}" }
                    if (result != "value-${key.value}") correct.set(false)
                }
            }
        }

        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        assertTrue(correct.get())
    }
}
