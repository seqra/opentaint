package org.opentaint.ir.impl.python.transforms.closure

object ClosureRuntime {
    const val SELF_PARAM_NAME = "<self>"
    const val CELL_LOCAL_PREFIX = "\$cell\$"

    const val CELL_CLASS_NAME = "<pir_cell>"
    const val CELL_VALUE_ATTR_NAME = "value"

    fun cellLocalName(name: String): String = "$CELL_LOCAL_PREFIX$name"

    fun capturedOrder(closureVars: Set<String>): List<String> = closureVars.sorted()

    fun adapterClassQn(moduleName: String, fnName: String): String =
        "$moduleName.<closure_$fnName>"

    fun implFunctionQn(moduleName: String, fnName: String): String =
        "$moduleName.<closure_${fnName}_impl>"
}
