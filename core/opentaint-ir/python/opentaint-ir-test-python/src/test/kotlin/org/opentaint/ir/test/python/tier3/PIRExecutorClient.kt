package org.opentaint.ir.test.python.tier3

import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRServerConnection
import org.opentaint.ir.impl.python.proto.ExecuteFunctionRequest
import org.opentaint.ir.impl.python.proto.ExecuteFunctionResponse
import java.io.Closeable

class PIRExecutorClient(settings: PIRSettings) : Closeable {

    private val connection = PIRServerConnection.open(settings)

    fun executeFunction(request: ExecuteFunctionRequest): ExecuteFunctionResponse =
        connection.executeFunction(request)

    override fun close() = connection.close()
}
