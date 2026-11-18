package org.opentaint.project

import mu.KLogging
import org.zeroturnaround.exec.ProcessExecutor
import org.zeroturnaround.exec.stream.slf4j.Slf4jStream
import java.nio.file.Path
import java.util.concurrent.TimeUnit
import kotlin.io.path.Path

object GoToolchain {
    private val logger = object : KLogging() {}.logger

    fun resolve(workDir: Path): Path? = try {
        val goRoot = ProcessExecutor()
            .command("go", "env", "GOROOT")
            .directory(workDir.toFile())
            // Without it `go` can report a toolchain that it downloaded into the module cache.
            .environment("GOTOOLCHAIN", "local")
            .readOutput(true)
            .redirectError(Slf4jStream.of(logger.underlyingLogger).asDebug())
            .exitValueNormal()
            .timeout(60, TimeUnit.SECONDS)
            .execute()
            .outputUTF8().trim()
        logger.info { "Go toolchain: $goRoot" }
        Path(goRoot)
    } catch (ex: Exception) {
        logger.warn { "No Go toolchain: failed to run `go env GOROOT`: ${(ex.cause ?: ex).message}" }
        null
    }
}
