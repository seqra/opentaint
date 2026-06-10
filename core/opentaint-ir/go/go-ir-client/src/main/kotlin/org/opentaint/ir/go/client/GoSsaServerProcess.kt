package org.opentaint.ir.go.client

import io.grpc.ManagedChannel
import io.grpc.ManagedChannelBuilder
import java.io.BufferedReader
import java.io.InputStreamReader
import java.util.concurrent.TimeUnit

/**
 * Manages the go-ssa-server subprocess lifecycle.
 */
class GoSsaServerProcess(
    private val serverBinaryPath: String =
        System.getProperty("goir.server.binary")
            ?: System.getenv("GOIR_SERVER_BINARY")
            ?: error("GOIR_SERVER_BINARY not set"),
) : AutoCloseable {
    private var process: Process? = null
    private var channel: ManagedChannel? = null

    /**
     * Continuously drains the server's stderr so it can never block on a full
     * pipe, while retaining the tail for crash diagnostics. The Go server writes
     * panics, fatal runtime errors (including the Go-side OOM trace) and signal
     * notifications here, so this is our primary window into *why* the process
     * died when gRPC merely reports "UNAVAILABLE: Network closed".
     */
    private var stderrCollector: ProcessStreamCollector? = null

    fun start(): ManagedChannel {
        val pb = ProcessBuilder(serverBinaryPath, "-port=0")
            .redirectInput(ProcessBuilder.Redirect.PIPE)
            .redirectErrorStream(false)

        val proc = pb.start()
        process = proc

        // Start draining stderr immediately, before any blocking read on stdout,
        // so early server-side failures are captured rather than discarded.
        stderrCollector = ProcessStreamCollector(proc.errorStream, "go-ssa-server-stderr").also { it.start() }

        // Read the port from stdout
        val reader = BufferedReader(InputStreamReader(proc.inputStream))
        val line = reader.readLine()
            ?: throw IllegalStateException(
                "Go server did not produce output (exited=${exitInfo()}).${stderrSuffix()}"
            )

        val port = if (line.startsWith("LISTENING:")) {
            line.substringAfter("LISTENING:").trim().toInt()
        } else {
            throw IllegalStateException("Unexpected server output: $line${stderrSuffix()}")
        }

        val ch = ManagedChannelBuilder.forAddress("localhost", port)
            .usePlaintext()
            .maxInboundMessageSize(256 * 1024 * 1024) // 256 MB
            .build()

        channel = ch
        return ch
    }

    /** Tail of the server's stderr captured so far, or `null` if unavailable. */
    fun stderrTail(): String? = stderrCollector?.snapshot()?.takeIf { it.isNotBlank() }

    /**
     * Best-effort description of the process exit state for diagnostics:
     * `"alive"`, `"exit=<code>"`, or `"unknown"`.
     */
    fun exitInfo(): String {
        val p = process ?: return "unknown"
        return if (p.isAlive) "alive" else "exit=${runCatching { p.exitValue() }.getOrNull() ?: "unknown"}"
    }

    /**
     * Builds a human-readable diagnostics block describing how the server
     * process ended together with the captured stderr tail. Intended to be
     * appended to client-side gRPC failures so CI logs explain the crash.
     */
    fun diagnostics(): String {
        // Give a process that just crashed a brief moment to flush stderr and
        // reach a terminal state, so the snapshot is as complete as possible.
        process?.let { runCatching { it.waitFor(500, TimeUnit.MILLISECONDS) } }
        val tail = stderrTail()
        return buildString {
            append("go-ssa-server process: ").append(exitInfo())
            if (tail != null) {
                append("\n--- go-ssa-server stderr (tail) ---\n")
                append(tail)
                append("\n--- end go-ssa-server stderr ---")
            } else {
                append("; no stderr captured")
            }
        }
    }

    private fun stderrSuffix(): String = stderrTail()?.let { "\nServer stderr:\n$it" } ?: ""

    override fun close() {
        channel?.let {
            it.shutdown()
            try {
                it.awaitTermination(5, TimeUnit.SECONDS)
            } catch (_: InterruptedException) {
                it.shutdownNow()
            }
        }
        process?.let {
            // Closing stdin signals the Go server to shut down via its
            // stdin-EOF watcher (mechanism A) before we resort to SIGTERM.
            try {
                it.outputStream.close()
            } catch (_: Throwable) {
                // best-effort
            }
            it.destroy()
            try {
                it.waitFor(5, TimeUnit.SECONDS)
            } catch (_: InterruptedException) {
                it.destroyForcibly()
            }
        }
        stderrCollector?.close()
        channel = null
        process = null
        stderrCollector = null
    }
}
