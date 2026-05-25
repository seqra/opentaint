package org.opentaint.ir.go.client

import org.opentaint.ir.go.proto.CloseSessionRequest
import org.opentaint.ir.go.proto.GoSSAServiceGrpc
import org.opentaint.ir.go.proto.LoadFunctionBodyRequest
import org.opentaint.ir.go.proto.LoadPackageRequest

/** Client-side owner for one lazy Go SSA server session. */
internal class GoIRLazySession(
    private val stub: GoSSAServiceGrpc.GoSSAServiceBlockingStub,
    val sessionId: String,
    private val deserializer: GoIRDeserializer,
    private val owner: GoIRClient,
) : AutoCloseable {
    private val loadLock = Any()
    private val loadedPackages = mutableSetOf<Int>()
    private val loadedFunctionBodies = mutableSetOf<Int>()
    @Volatile private var closed = false

    fun loadPackage(packageId: Int) {
        if (packageId in loadedPackages) return
        synchronized(loadLock) {
            checkOpen()
            if (packageId in loadedPackages) return
            val request = LoadPackageRequest.newBuilder()
                .setSessionId(sessionId)
                .setPackageId(packageId)
                .build()
            deserializer.mergePackageResponses(stub.loadPackage(request))
            loadedPackages.add(packageId)
        }
    }

    fun loadFunctionBody(functionId: Int) {
        if (functionId in loadedFunctionBodies) return
        synchronized(loadLock) {
            checkOpen()
            if (functionId in loadedFunctionBodies) return
            val request = LoadFunctionBodyRequest.newBuilder()
                .setSessionId(sessionId)
                .setFunctionId(functionId)
                .build()
            deserializer.mergeFunctionBodyResponses(stub.loadFunctionBody(request))
            loadedFunctionBodies.add(functionId)
        }
    }

    override fun close() {
        if (closed) return
        synchronized(loadLock) {
            if (closed) return
            stub.closeSession(
                CloseSessionRequest.newBuilder()
                    .setSessionId(sessionId)
                    .build(),
            )
            closed = true
        }
        owner.cleanupClosedSession(this)
    }

    private fun checkOpen() {
        check(!closed) { "Go IR lazy session is closed" }
    }
}
