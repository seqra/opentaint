package org.opentaint.ir.go.api

import org.opentaint.ir.go.type.GoIRAnonymousInterfaceType

/**
 * Top-level entity: a loaded Go program with all its packages.
 */
interface GoIRProgram {
    val packages: Map<String, GoIRPackage>  // keyed by import path
    val anonymousInterfaces: Map<Int, GoIRAnonymousInterfaceType>

    fun findPackage(importPath: String): GoIRPackage?
    fun allFunctions(): List<GoIRFunction>
    fun allNamedTypes(): List<GoIRNamedType>
    fun mainPackage(): GoIRPackage?
}
