package org.opentaint.dataflow.configuration.python.serialized

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.decodeFromStream
import kotlinx.serialization.Serializable
import java.io.InputStream

@Serializable
data class SerializedPythonTaintConfig(
    val entryPoint: List<SerializedPythonEntryPointSource> = emptyList(),
    val source: List<SerializedPythonSource> = emptyList(),
    val sink: List<SerializedPythonSink> = emptyList(),
    val methodExitSink: List<SerializedPythonExitSink> = emptyList(),
    val passThrough: List<SerializedPythonPassThrough> = emptyList(),
    val cleaner: List<SerializedPythonCleaner> = emptyList(),
)

fun loadSerializedPythonTaintConfig(stream: InputStream): SerializedPythonTaintConfig {
    val yaml = Yaml(configuration = YamlConfiguration(codePointLimit = Int.MAX_VALUE))
    return yaml.decodeFromStream<SerializedPythonTaintConfig>(stream)
}
