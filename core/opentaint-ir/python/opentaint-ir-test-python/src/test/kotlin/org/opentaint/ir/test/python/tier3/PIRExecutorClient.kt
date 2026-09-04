package org.opentaint.ir.test.python.tier3

import io.grpc.ManagedChannel
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRChannelFactory
import org.opentaint.ir.impl.python.PIRProcessManager
import org.opentaint.ir.impl.python.proto.ExecuteFunctionRequest
import org.opentaint.ir.impl.python.proto.ExecuteFunctionResponse
import org.opentaint.ir.impl.python.proto.PIRServiceGrpc
import org.opentaint.ir.impl.python.proto.PingRequest
import java.io.Closeable
import java.util.concurrent.TimeUnit

class PIRExecutorClient(private val settings: PIRSettings) : Closeable {

    private val processManager = PIRProcessManager(
        pythonExecutable = settings.pythonExecutable,
        serverModule = settings.serverModule,
        startupTimeout = settings.serverStartupTimeout,
    )
    private val channel: ManagedChannel

    init {
        val port = processManager.start()
        try {
            channel = PIRChannelFactory.forPort(port)
            PIRServiceGrpc.newBlockingStub(channel)
                .withDeadlineAfter(10, TimeUnit.SECONDS)
                .ping(PingRequest.getDefaultInstance())
        } catch (e: Throwable) {
            processManager.close()
            throw e
        }
    }

    fun executeFunction(request: ExecuteFunctionRequest): ExecuteFunctionResponse =
        PIRServiceGrpc.newBlockingStub(channel)
            .withDeadlineAfter(settings.rpcTimeout.toMillis(), TimeUnit.MILLISECONDS)
            .executeFunction(request)

    override fun close() {
        channel.shutdownNow()
        processManager.close()
    }
}
