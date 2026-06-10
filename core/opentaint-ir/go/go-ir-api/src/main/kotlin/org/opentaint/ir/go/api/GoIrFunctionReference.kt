package org.opentaint.ir.go.api

import org.opentaint.ir.go.type.GoIRFuncType

data class GoIrFunctionReference(
    val pkg: String,
    val name: String,
    val signature: GoIRFuncType
) {
    val fullName: String get() = "$pkg.$name"

    lateinit var program: GoIRProgram

    val function: GoIRFunction
        get() {
            val p = program.findPackage(pkg)
                ?: error("Could not find package $pkg for $fullName")
            // Match on name + signature because methods on different named
            // types legitimately share short names (e.g. `Dog.Legs` and
            // `Snake.Legs`); only the signature's receiver disambiguates them.
            return p.functions.firstOrNull { it.name == name && it.signature == signature }
                ?: error("Could not find function $fullName with signature $signature")
        }
}
