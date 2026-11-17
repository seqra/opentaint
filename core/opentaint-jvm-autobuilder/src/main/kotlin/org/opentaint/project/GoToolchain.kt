package org.opentaint.project

import mu.KLogging
import org.zeroturnaround.exec.ProcessExecutor
import org.zeroturnaround.exec.stream.slf4j.Slf4jStream
import java.nio.file.Path
import java.util.concurrent.TimeUnit
import kotlin.io.path.Path

object GoToolchain {
    private val logger = object : KLogging() {}.logger

    private const val GO_ENV_TIMEOUT_SECONDS = 60L

    /**
     * GOROOT of the Go installation on PATH, or `null` when there is no usable one.
     *
     * `GOTOOLCHAIN=local` keeps the answer on the installed Go: without it `go` can report a
     * toolchain that it downloaded into the module cache, and that path does not outlive the cache.
     */
    fun resolve(workDir: Path): Path? {
        val output = try {
            val result = ProcessExecutor()
                .command("go", "env", "GOROOT", "GOVERSION")
                .directory(workDir.toFile())
                .environment("GOTOOLCHAIN", "local")
                .readOutput(true)
                .redirectError(Slf4jStream.of(logger.underlyingLogger).asDebug())
                .timeout(GO_ENV_TIMEOUT_SECONDS, TimeUnit.SECONDS)
                .execute()

            if (result.exitValue != 0) {
                logger.warn { "No Go toolchain: `go env GOROOT` exited with ${result.exitValue}" }
                return null
            }

            result.outputUTF8().lines().map { it.trim() }.filter { it.isNotEmpty() }
        } catch (ex: Exception) {
            logger.warn { "No Go toolchain: failed to run `go env GOROOT`: ${(ex.cause ?: ex).message}" }
            return null
        }

        val goRoot = output.firstOrNull()?.let { Path(it) }
        if (goRoot == null || GoProject.goExecutable(goRoot) == null) {
            logger.warn { "No Go toolchain: `go env GOROOT` reported ${goRoot ?: "nothing"}, and it has no bin/go" }
            return null
        }

        logger.info { "Go toolchain: $goRoot (${output.getOrNull(1) ?: "unknown version"})" }
        return goRoot
    }
}
