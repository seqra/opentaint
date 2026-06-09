package org.opentaint.ir.go.api

/**
 * A Go package with its members.
 *
 * `isStdlib` and `isDependency` come from the SSA server's package summary.
 * `isProject` is the derived "neither" classification — packages declared by
 * the project being analyzed.
 */
interface GoIRPackage {
    val importPath: String
    val name: String
    val isStdlib: Boolean
    val isDependency: Boolean
    val isProject: Boolean get() = !isStdlib && !isDependency
    val functions: List<GoIRFunction>
    val namedTypes: List<GoIRNamedType>
    val globals: List<GoIRGlobal>
    val constants: List<GoIRConst>
    val imports: List<GoIRPackage>
    val initFunction: GoIRFunction?

    fun findNamedType(name: String): GoIRNamedType?
    fun findGlobal(name: String): GoIRGlobal?
    fun findConstant(name: String): GoIRConst?
    fun allMethods(): List<GoIRFunction>
}

/**
 * Set of packages that constitute the analysis scope.
 */
interface GoIRPackageSet {
    val program: GoIRProgram
    val packages: List<GoIRPackage>

    fun findPackage(importPath: String): GoIRPackage?
    fun findNamedType(fullName: String): GoIRNamedType?
    fun findFunction(fullName: String): GoIRFunction?
}
