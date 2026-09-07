package org.opentaint.ir.impl.python

import org.opentaint.ir.api.python.*
import org.opentaint.ir.impl.python.flatToPir.FlatToPirConverter
import org.opentaint.ir.impl.python.protoToFlat.ProtoToFlat
import org.opentaint.ir.impl.python.transforms.closure.FlatClosureTransformer

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

    private fun buildModules(connection: PIRServerConnection): List<PIRModule> {
        val iterator = connection.buildProject(settings.toBuildProjectRequest())
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
