package org.opentaint.ir.go.client

internal object GoIRGrpcLogging {
    private const val OPT_OUT_PROPERTY = "goir.grpc.logs"
    private const val GRPC_LOGGER = "io.grpc"

    @Volatile
    private var applied = false

    fun quietNoisyGrpcLogs() {
        if (applied) return
        synchronized(this) {
            if (applied) return
            applied = true
            if (System.getProperty(OPT_OUT_PROPERTY).equals("debug", ignoreCase = true)) return
            runCatching {
                val loggerFactory = Class.forName("org.slf4j.LoggerFactory")
                val logbackLogger = Class.forName("ch.qos.logback.classic.Logger")
                val levelClass = Class.forName("ch.qos.logback.classic.Level")
                val infoLevel = levelClass.getField("INFO").get(null)
                val logger = loggerFactory.getMethod("getLogger", String::class.java).invoke(null, GRPC_LOGGER)
                if (logbackLogger.isInstance(logger)) {
                    logbackLogger.getMethod("setLevel", levelClass).invoke(logger, infoLevel)
                }
            }
        }
    }
}
