package org.opentaint.ir.go.api

/** A package lookup interceptor. Unhandled requests are passed to the next resolver. */
interface GoIRTransformer {
    fun resolvePackage(importPath: String, next: () -> GoIRPackage?): GoIRPackage? = next()
    val additionalPackages: List<GoIRPackage> get() = emptyList()
}
