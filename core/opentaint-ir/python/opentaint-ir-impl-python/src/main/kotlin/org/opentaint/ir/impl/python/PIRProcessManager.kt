package org.opentaint.ir.impl.python

import java.io.BufferedReader
import java.io.Closeable
import java.io.InputStreamReader
import java.nio.file.Files
import java.nio.file.Path
import java.time.Duration
import java.util.concurrent.TimeUnit

class PIRProcessManager(
    private val pythonExecutable: String,
    private val serverModule: String = "pir_server",
    private val startupTimeout: Duration = Duration.ofSeconds(30),
) : Closeable {

    init {
        require(pythonExecutable.isNotBlank()) { "pythonExecutable must not be blank" }
    }

    private var process: Process? = null
    private var port: Int = -1
    private var workingDirectory: Path? = null

    fun start(): Int {
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

        val reader = BufferedReader(InputStreamReader(proc.inputStream))
        val deadline = System.currentTimeMillis() + startupTimeout.toMillis()

        while (System.currentTimeMillis() < deadline) {
            if (!proc.isAlive) {
                throw PIRServerStartupException(
                    "Python server exited with code ${proc.exitValue()}"
                )
            }
            val line = reader.readLine() ?: continue
            if (line.startsWith("READY:")) {
                port = line.substringAfter("READY:").trim().toInt()
                return port
            }
        }
        proc.destroyForcibly()
        throw PIRServerStartupException(
            "Python server did not become ready within $startupTimeout"
        )
    }

    fun getPort(): Int {
        check(port > 0) { "Server not started" }
        return port
    }

    override fun close() {
        val proc = process ?: return
        try {
            // Close stdin pipe — triggers the Python watchdog thread to exit
            try { proc.outputStream.close() } catch (_: Exception) {}
            if (proc.isAlive) {
                proc.waitFor(5, TimeUnit.SECONDS)
            }
        } finally {
            if (proc.isAlive) {
                proc.destroyForcibly()
                proc.waitFor(3, TimeUnit.SECONDS)
            }
            process = null
            port = -1
            workingDirectory?.let { runCatching { Files.deleteIfExists(it) } }
            workingDirectory = null
        }
    }

    val isRunning: Boolean get() = process?.isAlive == true
}

class PIRServerStartupException(message: String) : RuntimeException(message)
