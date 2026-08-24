package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.api.python.PIRDiagnostic
import org.opentaint.ir.api.python.PIRDiagnosticSeverity
import org.opentaint.ir.impl.python.flat.FlatFunctionIR

internal class ModuleContext(val moduleName: String) {

    private var lambdaCounter = 0
    private val nestedShadowCounters = mutableMapOf<Pair<String, String>, Int>()
    private val _registeredFunctions = mutableListOf<FlatFunctionIR>()
    private val _diagnostics = mutableListOf<PIRDiagnostic>()

    fun register(function: FlatFunctionIR) {
        _registeredFunctions.add(function)
    }

    fun freshLambdaName(): String = "<lambda>\$${lambdaCounter++}"

    fun freshNestedName(parentName: String, shortName: String): String {
        val key = parentName to shortName
        val count = nestedShadowCounters.getOrDefault(key, 0)
        nestedShadowCounters[key] = count + 1
        val base = "$parentName$$shortName"
        return if (count == 0) base else "$base$${count + 1}"
    }

    val imports: ImportManager = ImportManager()

    fun reportError(message: String, source: String, code: String) {
        _diagnostics.add(PIRDiagnostic(PIRDiagnosticSeverity.ERROR, message, source, code))
    }

    fun reportException(prefix: String, source: String, e: Throwable) {
        reportError("$prefix: ${e.javaClass.simpleName}: ${e.message}", source, e.javaClass.simpleName)
    }

    val registeredFunctions: List<FlatFunctionIR> get() = _registeredFunctions.toList()

    val diagnostics: List<PIRDiagnostic> get() = _diagnostics.toList()
}
