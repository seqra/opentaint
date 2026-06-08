package org.opentaint.dataflow.configuration.go.serialized

data class GoSerializedTaintConfig(
    val globalSource: List<GoSerializedGlobalSource> = emptyList(),
    val fieldSource: List<GoSerializedFieldSource> = emptyList(),
    val source: List<GoSerializedRule.Source> = emptyList(),
    val sink: List<GoSerializedRule.Sink> = emptyList(),
    val passThrough: List<GoSerializedRule.PassThrough> = emptyList(),
    val cleaner: List<GoSerializedRule.Cleaner> = emptyList(),
)