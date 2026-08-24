package org.opentaint.ir.impl.python.transforms.closure

object ClosureRuntime {
    const val SELF_PARAM_NAME = "<self>"
    const val CLOSURE_ATTR_NAME = "_closure_env_"
    const val CELL_CTOR_NAME = "__pir_cell__"
    const val CELL_VALUE_ATTR = "value"

    fun adapterClassQn(moduleName: String, fnName: String): String =
        "$moduleName.<closure_$fnName>"

    fun implFunctionQn(moduleName: String, fnName: String): String =
        "$moduleName.<closure_${fnName}_impl>"
}
