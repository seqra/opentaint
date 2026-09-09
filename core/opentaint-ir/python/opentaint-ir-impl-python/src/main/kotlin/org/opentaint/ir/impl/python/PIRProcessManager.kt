package org.opentaint.ir.impl.python

import java.io.BufferedReader
import java.io.Closeable
import java.io.InputStreamReader
import java.nio.file.Files
import java.nio.file.Path
import kotlin.time.Duration
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ExecutionException
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

class PIRProcessManager(
    private val pythonExecutable: String,
    private val startupTimeout: Duration,
    private val serverModule: String = "pir_server",
) : Closeable {

    init {
        require(pythonExecutable.isNotBlank()) { "pythonExecutable must not be blank" }
    }

    private var process: Process? = null

    private var workingDirectory: Path? = null

    fun start(): Int {
        check(process == null) { "Server already started" }

        // mypy always adds the process cwd to its package bases, so run the server in an
        // empty dir that can never be an ancestor of the sources being analyzed.
        val cwd = Files.createTempDirectory("pir-server-cwd")
        this.workingDirectory = cwd

        val pb = ProcessBuilder(pythonExecutable, "-m", serverModule, "--port", "0")
        pb.directory(cwd.toFile())
        pb.redirectErrorStream(false)
        pb.redirectError(ProcessBuilder.Redirect.INHERIT)

        val proc = pb.start()
        this.process = proc

        val ready = CompletableFuture<Int>()
        Thread({ drainStdout(proc, ready) }, "pir-server-stdout").apply {
            isDaemon = true
            start()
        }

        try {
            return ready.get(startupTimeout.inWholeMilliseconds, TimeUnit.MILLISECONDS)
        } catch (e: TimeoutException) {
            proc.destroyForcibly()
            throw PIRServerStartupException("Python server did not become ready within $startupTimeout")
        } catch (e: ExecutionException) {
            proc.destroyForcibly()
            throw e.cause as? PIRServerStartupException
                ?: PIRServerStartupException("Python server failed to start", e.cause)
        }
    }

    private fun drainStdout(proc: Process, ready: CompletableFuture<Int>) {
        try {
            BufferedReader(InputStreamReader(proc.inputStream)).use { reader ->
                // Keep reading past READY — once the 64 KB pipe buffer fills, the server
                // blocks forever inside its next write to stdout.
                while (true) {
                    val line = reader.readLine() ?: break
                    if (ready.isDone || !line.startsWith("READY:")) continue
                    val parsed = line.substringAfter("READY:").trim().toIntOrNull()
                    if (parsed == null || parsed <= 0) {
                        ready.completeExceptionally(
                            PIRServerStartupException("Malformed READY line from Python server: $line")
                        )
                    } else {
                        ready.complete(parsed)
                    }
                }
            }
        } catch (e: Exception) {
            ready.completeExceptionally(e)
        }
        if (!ready.isDone) {
            ready.completeExceptionally(PIRServerStartupException(exitMessage(proc)))
        }
    }

    private fun exitMessage(proc: Process): String =
        if (proc.waitFor(2, TimeUnit.SECONDS)) {
            "Python server exited with code ${proc.exitValue()} before becoming ready"
        } else {
            "Python server closed stdout before becoming ready"
        }

    override fun close() {
        try {
            process?.let { proc ->
                try {
                    // Close stdin pipe — triggers the Python watchdog thread to exit
                    try { proc.outputStream.close() } catch (_: Exception) {}
                    if (proc.isAlive) {
                        proc.waitFor(1, TimeUnit.SECONDS)
                    }
                } finally {
                    if (proc.isAlive) {
                        proc.destroyForcibly()
                        proc.waitFor(1, TimeUnit.SECONDS)
                    }
                }
            }
        } finally {
            process = null
            workingDirectory?.let { runCatching { deleteRecursively(it) } }
            workingDirectory = null
        }
    }

    private fun deleteRecursively(dir: Path) {
        Files.walk(dir).use { paths ->
            paths.sorted(Comparator.reverseOrder()).forEach { Files.deleteIfExists(it) }
        }
    }

    val isRunning: Boolean get() = process?.isAlive == true
}

class PIRServerStartupException(
    message: String,
    cause: Throwable? = null,
) : RuntimeException(message, cause)
