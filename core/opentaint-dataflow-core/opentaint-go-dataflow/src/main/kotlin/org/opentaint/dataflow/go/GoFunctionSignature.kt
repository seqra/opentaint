package org.opentaint.dataflow.go

import org.opentaint.ir.go.type.GoIRType

data class GoFunctionSignature(
    val name: String,
    val receiverType: GoIRType?,
    val paramTypes: List<GoIRType>,
    val resultType: GoIRType,
) {
    val arity: Int get() = paramTypes.size
    val hasReceiver: Boolean get() = receiverType != null
}

data class GoFieldSignature(
    val name: String,
    val type: GoIRType
)

data class GoGlobalFieldSignature(
    val name: String,
    val type: GoIRType
)
