package org.opentaint.ir.go.api

import org.opentaint.ir.go.type.GoIRFuncType

data class GoIrFunctionReference(
    val pkg: String,
    val fullName: String,
    val signature: GoIRFuncType
) {
    lateinit var program: GoIRProgram

    val function: GoIRFunction by lazy {
        program.lookup.function(this)
            ?: error("Could not find function $fullName with signature $signature")
    }
}

fun GoIRFunction.reference(): GoIrFunctionReference =
    GoIrFunctionReference(pkg?.importPath.orEmpty(), fullName, signature)
