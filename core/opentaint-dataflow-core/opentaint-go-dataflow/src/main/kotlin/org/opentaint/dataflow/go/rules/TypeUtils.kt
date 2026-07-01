package org.opentaint.dataflow.go.rules

import org.opentaint.ir.go.api.GoIRInterfaceMethod
import org.opentaint.ir.go.api.GoIRNamedType
import org.opentaint.ir.go.type.GoIRFuncType
import org.opentaint.ir.go.type.GoIRNamedTypeKind
import org.opentaint.ir.go.type.GoIRNamedTypeRef
import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.GoIRType

fun matchesType(valueType: GoIRType, typeName: String): Boolean {
    if (valueType.displayName == typeName) return true

    if (typeName.startsWith("*")) {
        if (valueType !is GoIRPointerType) return false
        return matchesType(valueType.elem, typeName.removePrefix("*"))
    }

    if (valueType !is GoIRPointerType) {
        val (valuePkg, valueSimple) = valueType.displayName.splitFullName()
        val (typePkg, typeSimple) = typeName.splitFullName()

        if (typeSimple == valueSimple && matchesPackage(valuePkg, typePkg)) return true
    }

    return implementsInterface(valueType, typeName)
}

private fun matchesPackage(valuePkg: String, typePkg: String): Boolean {
    if (valuePkg == typePkg) return true
    if (typePkg.isEmpty() || typePkg.contains('/')) return false
    return valuePkg.split('/').endsWith(typePkg.split('/'))
}

private fun implementsInterface(valueType: GoIRType, interfaceName: String): Boolean = runCatching {
    val (concreteRef, pointerReceiver) = namedTypeRef(valueType) ?: return false

    val (interfacePkg, interfaceSimple) = interfaceName.splitFullName()

    val program = concreteRef.typeRef.program

    val interfaceType = program
        .findPackage(interfacePkg)
        ?.findNamedType(interfaceSimple)
        ?: return false

    if (interfaceType.kind != GoIRNamedTypeKind.INTERFACE) return false

    val required = transitiveInterfaceMethods(interfaceType)
    if (required.isEmpty()) return false

    val concrete = concreteRef.namedType
    val provided = if (pointerReceiver) concrete.allMethods() else concrete.methods
    val providedMethods = provided.groupBy { it.name }

    required.all { req ->
        providedMethods[req.name]?.any { signaturesMatch(it.signature, req.signature) } ?: false
    }
}.getOrDefault(false)

private fun namedTypeRef(type: GoIRType): Pair<GoIRNamedTypeRef, Boolean>? = when (type) {
    is GoIRNamedTypeRef -> type to false
    is GoIRPointerType -> (type.elem as? GoIRNamedTypeRef)?.let { it to true }
    else -> null
}

private fun transitiveInterfaceMethods(interfaceType: GoIRNamedType): List<GoIRInterfaceMethod> {
    val result = mutableListOf<GoIRInterfaceMethod>()
    val seen = hashSetOf<String>()

    fun visit(type: GoIRNamedType) {
        if (!seen.add(type.fullName)) return
        result += type.interfaceMethods
        type.embeddedInterfaces.forEach { visit(it) }
    }

    visit(interfaceType)
    return result
}

private fun signaturesMatch(actual: GoIRFuncType, expected: GoIRFuncType): Boolean {
    if (actual.isVariadic != expected.isVariadic) return false
    if (actual.params.size != expected.params.size) return false
    if (actual.results.size != expected.results.size) return false
    if (actual.params.zip(expected.params).any { (a, e) -> a.displayName != e.displayName }) return false
    if (actual.results.zip(expected.results).any { (a, e) -> a.displayName != e.displayName }) return false
    return true
}

private fun <T> List<T>.endsWith(other: List<T>): Boolean {
    if (other.size > size) return false
    return other.asReversed().zip(this.asReversed()).all { (o, t) -> o == t }
}

fun String.splitFullName(): Pair<String, String> {
    val simpleName = substringAfterLast('.')
    val pkgName = substringBeforeLast('.', "")
    return pkgName to simpleName
}
