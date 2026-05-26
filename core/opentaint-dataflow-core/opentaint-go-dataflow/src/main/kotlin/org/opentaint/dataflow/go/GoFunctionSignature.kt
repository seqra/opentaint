package org.opentaint.dataflow.go

data class GoFunctionSignature(
    val name: String,
    val receiverType: String?,
    val paramTypes: List<String>,
    val resultType: String,
) {
    val arity: Int get() = paramTypes.size
    val hasReceiver: Boolean get() = receiverType != null
}
