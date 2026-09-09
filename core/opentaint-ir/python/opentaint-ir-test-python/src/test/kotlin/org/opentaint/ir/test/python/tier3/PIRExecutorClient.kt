package org.opentaint.ir.test.python.tier3

import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRServerConnection
import org.opentaint.ir.impl.python.proto.ExecuteFunctionRequest
import org.opentaint.ir.impl.python.proto.ExecuteFunctionResponse
import java.io.Closeable
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class PIRExecutorClient(settings: PIRSettings) : Closeable {

    private val connection = PIRServerConnection.open(settings)

    fun executeFunction(request: ExecuteFunctionRequest): ExecuteFunctionResponse =
        connection.executeFunction(request, EXECUTE_TIMEOUT)

    override fun close() = connection.close()

    private companion object {
        val EXECUTE_TIMEOUT: Duration = 120.seconds
    }
}
