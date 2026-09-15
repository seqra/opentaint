package org.opentaint.ir.impl.python.transforms.closure

object ClosureRuntime {
    const val SELF_PARAM_NAME = "<self>"
    const val ENV_LOCAL_NAME = "\$env"
    const val CELL_LOCAL_PREFIX = "\$cell\$"

    const val ENV_ATTR_NAME = "env"
    const val CELL_CLASS_NAME = "<pir_cell>"
    const val CELL_VALUE_ATTR_NAME = "value"

    fun cellLocalName(name: String): String = "$CELL_LOCAL_PREFIX$name"

    fun adapterClassQn(moduleName: String, fnName: String): String =
        "$moduleName.<closure_$fnName>"

    fun implFunctionQn(moduleName: String, fnName: String): String =
        "$moduleName.<closure_${fnName}_impl>"
}
