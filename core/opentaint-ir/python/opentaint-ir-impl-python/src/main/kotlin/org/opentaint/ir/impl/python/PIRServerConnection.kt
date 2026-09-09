package org.opentaint.ir.impl.python

import io.grpc.Context
import io.grpc.ManagedChannel
import io.grpc.Status
import io.grpc.StatusRuntimeException
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.proto.BuildProjectRequest
import org.opentaint.ir.impl.python.proto.ExecuteFunctionRequest
import org.opentaint.ir.impl.python.proto.ExecuteFunctionResponse
import org.opentaint.ir.impl.python.proto.MypyModuleProto
import org.opentaint.ir.impl.python.proto.PIRServiceGrpc
import org.opentaint.ir.impl.python.proto.PingRequest
import java.io.Closeable
import java.util.concurrent.TimeUnit
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class PIRServerConnection private constructor(
    private val buildTimeout: Duration,
    private val processManager: PIRProcessManager,
    private val channel: ManagedChannel,
    val pythonVersion: String,
    val mypyVersion: String,
) : Closeable {

    private var closed = false

    fun <T> buildProject(
        request: BuildProjectRequest,
        drain: (Iterator<MypyModuleProto>) -> T,
    ): T = Context.current().withCancellation().use { cancellable ->
        try {
            cancellable.call { drain(stub(buildTimeout).buildProject(request)) }
        } catch (e: StatusRuntimeException) {
            throw translate(e)
        }
    }

    private fun translate(e: StatusRuntimeException): RuntimeException = when (e.status.code) {
        Status.Code.INVALID_ARGUMENT ->
            PIRBuildException(e.status.description ?: e.message.orEmpty(), e)
        Status.Code.DEADLINE_EXCEEDED ->
            PIRBuildException(
                "PIR build exceeded buildTimeout of $buildTimeout; raise PIRSettings.buildTimeout",
                e,
            )
        else -> e
    }

    fun executeFunction(request: ExecuteFunctionRequest, timeout: Duration): ExecuteFunctionResponse =
        stub(timeout).executeFunction(request)

    override fun close() {
        closed = true
        try {
            shutdown(channel)
        } finally {
            processManager.close()
        }
    }

    private fun stub(timeout: Duration): PIRServiceGrpc.PIRServiceBlockingStub {
        check(!closed) { "Connection is closed" }
        return newStub(channel, timeout)
    }

    companion object {
        private val HANDSHAKE_TIMEOUT: Duration = 1.seconds
        private val CHANNEL_TERMINATION_TIMEOUT: Duration = 1.seconds

        fun open(settings: PIRSettings): PIRServerConnection {
            val processManager = PIRProcessManager(
                pythonExecutable = settings.pythonExecutable,
                serverModule = settings.serverModule,
                startupTimeout = settings.serverStartupTimeout,
            )
            var channel: ManagedChannel? = null
            try {
                channel = PIRChannelFactory.forPort(processManager.start())
                val ping = handshake(processManager, channel)
                return PIRServerConnection(
                    buildTimeout = settings.buildTimeout,
                    processManager = processManager,
                    channel = channel,
                    pythonVersion = ping.pythonVersion,
                    mypyVersion = ping.mypyVersion,
                )
            } catch (e: Throwable) {
                channel?.let { runCatching { shutdown(it) } }
                processManager.close()
                throw e
            }
        }

        private fun handshake(
            processManager: PIRProcessManager,
            channel: ManagedChannel,
        ): PingResult {
            val response = try {
                newStub(channel, HANDSHAKE_TIMEOUT).ping(PingRequest.getDefaultInstance())
            } catch (e: Exception) {
                if (processManager.isRunning) throw e
                throw PIRServerStartupException("Python server died before ping", e)
            }
            return PingResult(response.pythonVersion, response.mypyVersion)
        }

        private fun newStub(
            channel: ManagedChannel,
            timeout: Duration,
        ): PIRServiceGrpc.PIRServiceBlockingStub =
            PIRServiceGrpc.newBlockingStub(channel)
                .withDeadlineAfter(timeout.inWholeMilliseconds, TimeUnit.MILLISECONDS)

        private fun shutdown(channel: ManagedChannel) {
            channel.shutdown()
            if (!channel.awaitTermination(CHANNEL_TERMINATION_TIMEOUT.inWholeSeconds, TimeUnit.SECONDS)) {
                channel.shutdownNow()
                channel.awaitTermination(CHANNEL_TERMINATION_TIMEOUT.inWholeSeconds, TimeUnit.SECONDS)
            }
        }
    }

    private data class PingResult(val pythonVersion: String, val mypyVersion: String)
}

fun PIRSettings.toBuildProjectRequest(): BuildProjectRequest =
    BuildProjectRequest.newBuilder()
        .addAllSources(sources)
        .addAllMypyFlags(mypyFlags)
        .setPythonVersion(pythonVersion ?: "")
        .addAllPackageRoots(packageRoots)
        .build()

class PIRBuildException(
    message: String,
    cause: Throwable? = null,
) : RuntimeException(message, cause)
