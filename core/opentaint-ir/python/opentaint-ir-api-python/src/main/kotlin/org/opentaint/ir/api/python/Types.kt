package org.opentaint.ir.api.python

import org.opentaint.ir.api.common.CommonTypeName

sealed interface PIRType : CommonTypeName {
    override val typeName: String get() = toString()
}

data class PIRClassType(
    val qualifiedName: String,
    val typeArgs: List<PIRType> = emptyList(),
) : PIRType {
    override fun toString(): String = if (typeArgs.isEmpty()) qualifiedName
        else "$qualifiedName[${typeArgs.joinToString(", ")}]"
}

data class PIRFunctionType(
    val paramTypes: List<PIRType>,
    val returnType: PIRType,
) : PIRType {
    override fun toString(): String =
        "(${paramTypes.joinToString(", ")}) -> $returnType"
}

data class PIRUnionType(
    val members: List<PIRType>,
) : PIRType {
    override fun toString(): String =
        members.joinToString(" | ")
}

data class PIRTupleType(
    val elementTypes: List<PIRType>,
    val isVarLength: Boolean = false,
) : PIRType {
    override fun toString(): String = if (isVarLength && elementTypes.size == 1)
        "tuple[${elementTypes[0]}, ...]"
    else "tuple[${elementTypes.joinToString(", ")}]"
}

data class PIRLiteralType(
    val value: String,
    val baseType: PIRType,
) : PIRType {
    override fun toString(): String = "Literal[$value]"
}

data object PIRAnyType : PIRType {
    override fun toString(): String = "Any"
}

data object PIRNeverType : PIRType {
    override fun toString(): String = "Never"
}

data object PIRNoneType : PIRType {
    override fun toString(): String = "None"
}

data class PIRTypeVarType(
    val name: String,
    val bounds: List<PIRType> = emptyList(),
) : PIRType {
    override fun toString(): String = name
}
