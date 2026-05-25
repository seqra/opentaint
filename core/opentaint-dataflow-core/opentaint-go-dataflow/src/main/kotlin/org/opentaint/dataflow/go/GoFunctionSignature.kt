package org.opentaint.dataflow.go

data class GoFunctionSignature(
    val name: String,
    val numArgs: Int,
    val hasReceiver: Boolean,
)
