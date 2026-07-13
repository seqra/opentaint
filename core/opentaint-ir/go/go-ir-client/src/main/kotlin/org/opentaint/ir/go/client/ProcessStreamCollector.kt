package org.opentaint.ir.go.client

import java.io.BufferedReader
import java.io.InputStream
import java.io.InputStreamReader
import java.nio.charset.StandardCharsets

/**
 * Drains an [InputStream] (typically a subprocess's stderr) on a dedicated
 * daemon thread, retaining only the most recent [maxLines] lines in a bounded
 * ring buffer.
 *
 * Continuous draining is mandatory: if nobody reads the child's stderr, a
 * chatty process can fill the OS pipe buffer (~64 KiB) and block on its next
 * write, wedging the whole server. Bounded retention keeps memory predictable
 * even for very verbose output while still preserving the tail — which is
 * exactly where panics and fatal-runtime traces appear right before a crash.
 */
internal class ProcessStreamCollector(
    private val source: InputStream,
    threadName: String,
    private val maxLines: Int = 200,
) : AutoCloseable {
    private val lines = ArrayDeque<String>()
    private val thread = Thread(::pump, threadName).apply { isDaemon = true }

    fun start() {
        thread.start()
    }

    private fun pump() {
        try {
            BufferedReader(InputStreamReader(source, StandardCharsets.UTF_8)).forEachLine(::add)
        } catch (_: Throwable) {
            // Stream closed or the process is gone; nothing actionable here.
        }
    }

    @Synchronized
    private fun add(line: String) {
        lines.addLast(line)
        while (lines.size > maxLines) lines.removeFirst()
    }

    /** Returns the retained tail of the stream as a single newline-joined string. */
    @Synchronized
    fun snapshot(): String = lines.joinToString("\n")

    override fun close() {
        try {
            source.close()
        } catch (_: Throwable) {
            // best-effort
        }
    }
}
