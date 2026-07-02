package org.opentaint.dataflow.configuration.jvm.serialized

import kotlinx.serialization.Serializable

@Serializable
data class SerializedTaintConfig(
    val language: String? = null,
    val library: String? = null,
    val dependencies: List<String>? = null,
    val entryPoint: List<SerializedRule.EntryPoint>? = null,
    val source: List<SerializedRule.Source>? = null,
    val methodExitSource: List<SerializedRule.MethodExitSource>? = null,
    val sink: List<SerializedRule.Sink>? = null,
    val passThrough: List<SerializedRule.PassThrough>? = null,
    val cleaner: List<SerializedRule.Cleaner>? = null,
    val methodExitSink: List<SerializedRule.MethodExitSink>? = null,
    val methodEntrySink: List<SerializedRule.MethodEntrySink>? = null,
    val staticFieldSource: List<SerializedFieldRule.SerializedStaticFieldSource>? = null,
)
