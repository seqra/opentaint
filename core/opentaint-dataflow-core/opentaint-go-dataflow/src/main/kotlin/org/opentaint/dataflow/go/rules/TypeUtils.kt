package org.opentaint.dataflow.go.rules

import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.GoIRType

fun matchesType(valueType: GoIRType, typeName: String): Boolean {
    if (valueType.displayName == typeName) return true

    if (typeName.startsWith("*")) {
        if (valueType !is GoIRPointerType) return false
        return matchesType(valueType.elem, typeName.removePrefix("*"))
    }

    if (valueType is GoIRPointerType) return false

    val (valuePkg, valueSimple) = valueType.displayName.splitFullName()
    val (typePkg, typeSimple) = typeName.splitFullName()

    if (typeSimple != valueSimple) return false

    val valuePkgParts = valuePkg.split('/')
    val typePkgParts = typePkg.split('/')
    return valuePkgParts.endsWith(typePkgParts)
}

private fun <T> List<T>.endsWith(other: List<T>): Boolean =
    other.asReversed().zip(this.asReversed()).all { (o, t) -> o == t }

fun String.splitFullName(): Pair<String, String> {
    val simpleName = substringAfterLast('.')
    val pkgName = substringBeforeLast('.', "")
    return pkgName to simpleName
}
