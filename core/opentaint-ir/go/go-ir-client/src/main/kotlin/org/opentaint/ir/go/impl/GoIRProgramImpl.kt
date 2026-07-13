package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.*
import org.opentaint.ir.go.type.GoIRAnonymousInterfaceType

class GoIRProgramImpl(
    override val packages: Map<String, GoIRPackage>,
    override val anonymousInterfaces: Map<Int, GoIRAnonymousInterfaceType>,
) : GoIRProgram {
    override fun findPackage(importPath: String) = packages[importPath]

    override fun allFunctions(): List<GoIRFunction> =
        packages.values.flatMap { it.functions }

    override fun allNamedTypes(): List<GoIRNamedType> =
        packages.values.flatMap { it.namedTypes }

    override fun mainPackage(): GoIRPackage? =
        packages.values.find { it.name == "main" }
}
