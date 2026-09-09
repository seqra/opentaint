package org.opentaint.ir.impl.python

import mu.KotlinLogging
import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRDiagnosticSeverity
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRModule
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.flatToPir.FlatToPirConverter
import org.opentaint.ir.impl.python.proto.BuildEventProto
import org.opentaint.ir.impl.python.protoToFlat.ProtoToFlat
import org.opentaint.ir.impl.python.transforms.closure.FlatClosureTransformer
import kotlin.time.Duration.Companion.seconds
import kotlin.time.TimeSource

private val LOG_INTERVAL = 10.seconds

private val logger = KotlinLogging.logger {}

class PIRClasspathLoader(private val settings: PIRSettings) {

    fun load(): PIRClasspathImpl =
        PIRServerConnection.open(settings).use { connection ->
            val modules = if (settings.sources.isNotEmpty()) {
                buildModules(connection)
            } else {
                emptyList()
            }

            val index = indexModules(modules)

            PIRClasspathImpl(
                pythonVersion = connection.pythonVersion,
                mypyVersion = connection.mypyVersion,
                modules = modules,
                modulesByName = index.modulesByName,
                classesByQName = index.classesByQName,
                functionsByQName = index.functionsByQName,
            )
        }

    private fun buildModules(connection: PIRServerConnection): List<PIRModule> =
        connection.buildProject(settings.toBuildProjectRequest()) { iterator ->
            val result = mutableListOf<PIRModule>()
            var count = 0
            var lastLog = TimeSource.Monotonic.markNow()

            while (iterator.hasNext()) {
                val event = iterator.next()

                when (event.eventCase) {
                    BuildEventProto.EventCase.FAILURE -> {
                        logger.error { "Build failed: ${event.failure.errorsList.joinToString("; ")}" }
                        continue
                    }

                    BuildEventProto.EventCase.EVENT_NOT_SET -> {
                        logger.error { "Unrecognized build event" }
                        continue
                    }

                    BuildEventProto.EventCase.MODULE -> {  }
                }

                val astModuleProto = event.module
                val flat = ProtoToFlat.lowerModule(astModuleProto)
                val flatWithClosure = FlatClosureTransformer.transform(flat)
                val module = FlatToPirConverter(flatWithClosure).convert()
                logDiagnostics(module)
                result.add(module)
                count++

                if (lastLog.elapsedNow() >= LOG_INTERVAL) {
                    logger.info { "Built $count modules..." }
                    lastLog = TimeSource.Monotonic.markNow()
                }
            }
            logger.info { "Finished. $count modules built." }
            result
        }

    private fun logDiagnostics(module: PIRModule) {
        for (d in module.diagnostics) {
            val render = { "${d.functionName}: [${d.exceptionType}] ${d.message}" }
            when (d.severity) {
                PIRDiagnosticSeverity.ERROR -> logger.error(render)
                PIRDiagnosticSeverity.WARNING -> logger.warn(render)
            }
        }
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
