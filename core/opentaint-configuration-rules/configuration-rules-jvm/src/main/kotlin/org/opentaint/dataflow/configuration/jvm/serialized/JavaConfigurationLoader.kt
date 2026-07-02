package org.opentaint.dataflow.configuration.jvm.serialized

import com.charleskorn.kaml.YamlNode
import org.opentaint.dataflow.configuration.ConfigurationLoader

class JavaConfigurationLoader : ConfigurationLoader<SerializedTaintConfig> {
    override val language: String get() = "java"

    override fun load(node: YamlNode): SerializedTaintConfig =
        ConfigurationLoader.yaml.decodeFromYamlNode<SerializedTaintConfig>(node)

    override fun join(config: List<SerializedTaintConfig>) = SerializedTaintConfig(
        language = language,
        library = null,
        dependencies = config.flatMap { it.dependencies.orEmpty() },
        entryPoint = config.flatMap { it.entryPoint.orEmpty() },
        source = config.flatMap { it.source.orEmpty() },
        methodExitSource = config.flatMap { it.methodExitSource.orEmpty() },
        sink = config.flatMap { it.sink.orEmpty() },
        passThrough = config.flatMap { it.passThrough.orEmpty() },
        cleaner = config.flatMap { it.cleaner.orEmpty() },
        methodExitSink = config.flatMap { it.methodExitSink.orEmpty() },
        methodEntrySink = config.flatMap { it.methodEntrySink.orEmpty() },
        staticFieldSource = config.flatMap { it.staticFieldSource.orEmpty() },
    )
}
