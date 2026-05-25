package org.opentaint.dataflow.configuration.go.serialized

data class GoSerializedTaintConfig(
    val source: List<GoSerializedRule.Source> = emptyList(),
    val sink: List<GoSerializedRule.Sink> = emptyList(),
    val passThrough: List<GoSerializedRule.PassThrough> = emptyList(),
    val cleaner: List<GoSerializedRule.Cleaner> = emptyList(),
)