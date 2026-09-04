package org.opentaint.ir.impl.python

import io.grpc.ManagedChannel
import org.opentaint.ir.api.python.*
import org.opentaint.ir.impl.python.flatToPir.FlatToPirConverter
import org.opentaint.ir.impl.python.protoToFlat.ProtoToFlat
import org.opentaint.ir.impl.python.transforms.closure.FlatClosureTransformer
import org.opentaint.ir.impl.python.proto.BuildProjectRequest
import org.opentaint.ir.impl.python.proto.PIRServiceGrpc
import org.opentaint.ir.impl.python.proto.PingRequest
import java.util.concurrent.TimeUnit

class PIRClasspathLoader(private val settings: PIRSettings) {

    fun load(): PIRClasspathImpl =
        PIRProcessManager(
            pythonExecutable = settings.pythonExecutable,
            serverModule = settings.serverModule,
            startupTimeout = settings.serverStartupTimeout,
        ).use { processManager ->
            val channel = PIRChannelFactory.forPort(processManager.start())
            try {
                val versions = handshake(processManager, channel)

                val modules = if (settings.sources.isNotEmpty()) {
                    buildModules(channel)
                } else {
                    emptyList()
                }

                val index = indexModules(modules)

                PIRClasspathImpl(
                    pythonVersion = versions.pythonVersion,
                    mypyVersion = versions.mypyVersion,
                    modules = modules,
                    modulesByName = index.modulesByName,
                    classesByQName = index.classesByQName,
                    functionsByQName = index.functionsByQName,
                )
            } finally {
                channel.shutdownNow()
            }
        }

    private data class Versions(val pythonVersion: String, val mypyVersion: String)

    private fun handshake(processManager: PIRProcessManager, channel: ManagedChannel): Versions {
        val maxRetries = 5
        var lastException: Exception? = null
        for (attempt in 1..maxRetries) {
            if (!processManager.isRunning) {
                throw PIRServerStartupException(
                    "Python server died before ping (attempt $attempt/$maxRetries)"
                )
            }
            try {
                val pingStub = PIRServiceGrpc.newBlockingStub(channel)
                    .withDeadlineAfter(10, TimeUnit.SECONDS)
                val pingResponse = pingStub.ping(PingRequest.getDefaultInstance())
                return Versions(pingResponse.pythonVersion, pingResponse.mypyVersion)
            } catch (e: Exception) {
                lastException = e
                if (attempt < maxRetries) {
                    Thread.sleep(1000L * attempt)
                }
            }
        }
        throw lastException ?: IllegalStateException("Ping failed without exception")
    }

    private fun buildModules(channel: ManagedChannel): List<PIRModule> {
        val request = BuildProjectRequest.newBuilder()
            .addAllSources(settings.sources)
            .addAllMypyFlags(settings.mypyFlags)
            .setPythonVersion(settings.pythonVersion ?: "")
            .addAllPackageRoots(settings.packageRoots)
            .build()

        val stub = PIRServiceGrpc.newBlockingStub(channel)
            .withDeadlineAfter(settings.rpcTimeout.toMillis(), TimeUnit.MILLISECONDS)

        val iterator = stub.buildProject(request)
        val result = mutableListOf<PIRModule>()
        var count = 0
        var unknownCount = 0
        var lastLog = System.nanoTime()

        while (iterator.hasNext()) {
            val astModuleProto = iterator.next()

            if (astModuleProto.errorsCount > 0) {
                val diagnostics = astModuleProto.errorsList.map {
                    PIRDiagnostic(
                        PIRDiagnosticSeverity.ERROR,
                        it,
                        astModuleProto.name,
                        "MypyBuildError",
                    )
                }
                result.add(PIRUnknownModule(astModuleProto.name, diagnostics))
                unknownCount++
                continue
            }

            val flat = ProtoToFlat.lowerModule(astModuleProto)
            val flatWithClosure = FlatClosureTransformer.transform(flat)
            result.add(FlatToPirConverter(flatWithClosure).convert())
            count++

            val now = System.nanoTime()
            if (now - lastLog >= 10_000_000_000L) {
                System.err.println("PIR: Built $count modules ($unknownCount unknown)...")
                lastLog = now
            }
        }
        System.err.println("PIR: Finished. $count modules built, $unknownCount unknown.")
        return result
    }
}

private data class ModuleIndex(
    val modulesByName: Map<String, PIRModule>,
    val classesByQName: Map<String, PIRClass>,
    val functionsByQName: Map<String, PIRFunction>,
)

private fun indexModules(modules: List<PIRModule>): ModuleIndex {
    val modulesByName = mutableMapOf<String, PIRModule>()
    val classesByQName = mutableMapOf<String, PIRClass>()
    val functionsByQName = mutableMapOf<String, PIRFunction>()

    fun indexClass(cls: PIRClass) {
        classesByQName[cls.qualifiedName] = cls
        for (method in cls.methods) functionsByQName[method.qualifiedName] = method
        for (nested in cls.nestedClasses) indexClass(nested)
    }

    for (module in modules) {
        modulesByName[module.name] = module
        for (cls in module.classes) indexClass(cls)
        for (func in module.functions) functionsByQName[func.qualifiedName] = func
    }
    return ModuleIndex(modulesByName, classesByQName, functionsByQName)
}
