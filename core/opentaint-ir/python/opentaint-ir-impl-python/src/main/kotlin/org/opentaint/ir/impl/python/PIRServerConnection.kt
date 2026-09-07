package org.opentaint.ir.impl.python

import io.grpc.ManagedChannel
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
    private val rpcTimeout: Duration,
    private val processManager: PIRProcessManager,
    private val channel: ManagedChannel,
    val pythonVersion: String,
    val mypyVersion: String,
) : Closeable {

    fun buildProject(request: BuildProjectRequest): Iterator<MypyModuleProto> =
        stub().buildProject(request)

    fun executeFunction(request: ExecuteFunctionRequest): ExecuteFunctionResponse =
        stub().executeFunction(request)

    override fun close() {
        try {
            shutdown(channel)
        } finally {
            processManager.close()
        }
    }

    private fun stub(): PIRServiceGrpc.PIRServiceBlockingStub =
        PIRServiceGrpc.newBlockingStub(channel)
            .withDeadlineAfter(rpcTimeout.inWholeMilliseconds, TimeUnit.MILLISECONDS)

    companion object {
        private val HANDSHAKE_TIMEOUT: Duration = 10.seconds
        private val CHANNEL_TERMINATION_TIMEOUT: Duration = 5.seconds

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
                    rpcTimeout = settings.rpcTimeout,
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
                PIRServiceGrpc.newBlockingStub(channel)
                    .withDeadlineAfter(HANDSHAKE_TIMEOUT.inWholeMilliseconds, TimeUnit.MILLISECONDS)
                    .ping(PingRequest.getDefaultInstance())
            } catch (e: Exception) {
                if (processManager.isRunning) throw e
                throw PIRServerStartupException("Python server died before ping", e)
            }
            return PingResult(response.pythonVersion, response.mypyVersion)
        }

        private fun shutdown(channel: ManagedChannel) {
            channel.shutdownNow()
            channel.awaitTermination(CHANNEL_TERMINATION_TIMEOUT.inWholeSeconds, TimeUnit.SECONDS)
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
