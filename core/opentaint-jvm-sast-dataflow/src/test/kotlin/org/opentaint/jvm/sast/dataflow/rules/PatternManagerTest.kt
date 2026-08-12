package org.opentaint.jvm.sast.dataflow.rules

import java.util.concurrent.Executors
import kotlin.test.Test
import kotlin.test.assertSame

class PatternManagerTest {
    @Test
    fun `compiled patterns are shared between concurrent callers`() {
        val manager = PatternManager()
        val executor = Executors.newFixedThreadPool(8)

        try {
            val patterns = (0 until 1_000).map {
                executor.submit<Regex> { manager.compilePattern("foo.*bar") }
            }.map { it.get() }

            val expected = patterns.first()
            patterns.forEach { assertSame(expected, it) }
        } finally {
            executor.shutdownNow()
        }
    }
}
