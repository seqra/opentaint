package org.opentaint.dataflow.util

import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.concurrent.thread
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class ConcurrentReadSafeLongCollectionsTest {
    @Test
    fun `long map supports concurrent reads while single writer rehashes`() {
        val map = long2ObjectMap<Long>()
        val done = AtomicBoolean(false)
        val start = CountDownLatch(1)
        val failures = ConcurrentLinkedQueue<Throwable>()

        val readers = List(READER_COUNT) {
            thread(name = "long-map-reader-$it") {
                start.await()
                try {
                    while (!done.get()) {
                        map.forEachEntry { key, value -> assertEquals(key, value) }
                        map[PROBE_KEY]
                    }
                } catch (failure: Throwable) {
                    failures.add(failure)
                }
            }
        }

        val writer = thread(name = "long-map-writer") {
            start.await()
            try {
                map.put(0, 0)
                for (key in 1L..ENTRY_COUNT.toLong()) {
                    map.put(key, key)
                }
            } catch (failure: Throwable) {
                failures.add(failure)
            } finally {
                done.set(true)
            }
        }

        start.countDown()
        writer.join()
        readers.forEach(Thread::join)

        assertTrue(failures.isEmpty(), failures.joinToString("\n") { it.stackTraceToString() })
        val collected = HashMap<Long, Long>()
        map.forEachEntry { key, value -> collected[key] = value }
        assertEquals(ENTRY_COUNT + 1, collected.size)
        assertEquals(PROBE_KEY, collected[PROBE_KEY])
    }

    @Test
    fun `long set supports concurrent reads while single writer rehashes`() {
        val set = longSet()
        val done = AtomicBoolean(false)
        val start = CountDownLatch(1)
        val failures = ConcurrentLinkedQueue<Throwable>()

        val readers = List(READER_COUNT) {
            thread(name = "long-set-reader-$it") {
                start.await()
                try {
                    while (!done.get()) {
                        set.forEachLong { value -> assertTrue(value in 0L..ENTRY_COUNT.toLong()) }
                        set.contains(PROBE_KEY)
                    }
                } catch (failure: Throwable) {
                    failures.add(failure)
                }
            }
        }

        val writer = thread(name = "long-set-writer") {
            start.await()
            try {
                set.add(0)
                for (value in 1L..ENTRY_COUNT.toLong()) {
                    set.add(value)
                }
            } catch (failure: Throwable) {
                failures.add(failure)
            } finally {
                done.set(true)
            }
        }

        start.countDown()
        writer.join()
        readers.forEach(Thread::join)

        assertTrue(failures.isEmpty(), failures.joinToString("\n") { it.stackTraceToString() })
        val collected = HashSet<Long>()
        set.forEachLong(collected::add)
        assertEquals(ENTRY_COUNT + 1, collected.size)
        assertTrue(PROBE_KEY in collected)
    }

    private companion object {
        const val ENTRY_COUNT = 100_000
        const val READER_COUNT = 4
        const val PROBE_KEY = 73_421L
    }
}
