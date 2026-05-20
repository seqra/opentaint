package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.proto.GoSSAServiceGrpc
import org.opentaint.ir.go.proto.OpenSessionRequest
import java.nio.file.Path
import java.util.concurrent.ConcurrentHashMap

/**
 * Timing breakdown for a single IR build.
 *
 * Under the lazy `OpenSession` flow these timings reflect only the open call;
 * subsequent package and function-body materializations happen on demand and
 * are NOT included here. Specifically:
 *   - [serverBuildMs]: time the Go server reported for handling `OpenSession`.
 *   - [deserializeMs]: time spent processing the `OpenSessionResponse` on the
 *     Kotlin side (turning package summaries into lazy placeholders).
 *   - [totalMs]: wall-clock for the `OpenSession` RPC + the deserialize step
 *     above. It does NOT cover later lazy loads.
 */
data class BuildTimings(
    /** Total wall-clock time for `OpenSession` + deserialization of its response. */
    val totalMs: Long,
    /** Time spent on the Go server during `OpenSession`, from the Summary message. */
    val serverBuildMs: Long,
    /** Time spent deserializing the `OpenSessionResponse` on the Kotlin side. */
    val deserializeMs: Long,
)

/**
 * Result of an IR build, containing both the program and timing info.
 */
data class BuildResult(
    val program: GoIRProgram,
    val timings: BuildTimings,
)

/**
 * High-level API for loading Go IR from Go source code.
 */
class GoIRClient : AutoCloseable {
    private val serverProcess = GoSsaServerProcess()
    private val channel = serverProcess.start()
    private val stub = GoSSAServiceGrpc.newBlockingStub(channel)
    private val lazySessions = ConcurrentHashMap.newKeySet<GoIRLazySession>()

    /**
     * Build IR from a directory with Go source files.
     */
    fun buildFromDir(
        dir: Path,
        vararg patterns: String,
        instantiateGenerics: Boolean = true,
        sanityCheck: Boolean = true,
        includeStdlib: Boolean = false,
    ): GoIRProgram = buildFromDirWithTimings(dir, *patterns,
        instantiateGenerics = instantiateGenerics,
        sanityCheck = sanityCheck,
        includeStdlib = includeStdlib,
    ).program

    /**
     * Open a lazy IR session from a directory, returning the program (with
     * lazy package/body placeholders) and timings covering only `OpenSession`.
     */
    fun buildFromDirWithTimings(
        dir: Path,
        vararg patterns: String,
        instantiateGenerics: Boolean = true,
        sanityCheck: Boolean = true,
        includeStdlib: Boolean = false,
    ): BuildResult {
        val request = OpenSessionRequest.newBuilder()
            .addAllPatterns(patterns.toList())
            .setWorkingDir(dir.toAbsolutePath().toString())
            .setInstantiateGenerics(instantiateGenerics)
            .setSanityCheck(sanityCheck)
            .setIncludeStdlib(includeStdlib)
            .build()

        val totalStart = System.nanoTime()
        val response = stub.openSession(request)
        val deserializer = GoIRDeserializer()
        val deserializeStart = System.nanoTime()
        val program = deserializer.deserializeLazy(response) { d ->
            GoIRLazySession(stub, response.sessionId, d).also { lazySessions.add(it) }
        }
        val deserializeMs = (System.nanoTime() - deserializeStart) / 1_000_000
        val totalMs = (System.nanoTime() - totalStart) / 1_000_000

        return BuildResult(
            program = program,
            timings = BuildTimings(
                totalMs = totalMs,
                serverBuildMs = deserializer.serverBuildTimeMs,
                deserializeMs = deserializeMs,
            ),
        )
    }

    /**
     * Build IR from inline Go source code.
     * Creates a temp directory, writes source, and loads it.
     */
    fun buildFromSource(
        source: String,
        packageName: String = "p",
    ): GoIRProgram {
        val tmpDir = java.nio.file.Files.createTempDirectory("goir-test")
        try {
            val goFile = tmpDir.resolve("$packageName.go")
            goFile.toFile().writeText(source)
            tmpDir.resolve("go.mod").toFile().writeText("module test/$packageName\ngo 1.22\n")
            return buildFromDir(tmpDir, "./...")
        } finally {
            // Don't delete — may be useful for debugging
        }
    }

    override fun close() {
        lazySessions.forEach { session ->
            runCatching { session.close() }
        }
        lazySessions.clear()
        serverProcess.close()
    }
}
