package org.opentaint.config

import java.nio.file.FileSystems
import java.nio.file.Files
import java.util.Collections
import kotlin.streams.asSequence
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCleaner
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonEntryPointSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonPassThrough
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSink
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintConfig
import org.opentaint.dataflow.configuration.python.serialized.loadSerializedPythonTaintConfig

object PythonConfigLoader {
    private const val CONFIG_ROOT = "/python-config"
    private val config = lazy { loadConfig() }

    fun getConfig() = config.value

    private fun loadConfig(): SerializedPythonTaintConfig? {
        val resources = javaClass.getResource(CONFIG_ROOT) ?: return null
        val uri = resources.toURI()

        // it is expected to be used as a .jar-dependency
        if (uri.scheme != "jar") return null

        val allFiles =
            FileSystems.newFileSystem(uri, Collections.emptyMap<String, String>()).use { fs ->
                val path = fs.getPath(CONFIG_ROOT)
                Files.walk(path).asSequence().map { path.relativize(it).toString() }.toList()
            }
        if (allFiles.isEmpty()) return null
        val files = allFiles.filter { it.endsWith(".yaml") }

        val entryPoints = mutableListOf<SerializedPythonEntryPointSource>()
        val sources = mutableListOf<SerializedPythonSource>()
        val sinks = mutableListOf<SerializedPythonSink>()
        val passThroughs = mutableListOf<SerializedPythonPassThrough>()
        val cleaners = mutableListOf<SerializedPythonCleaner>()

        files.forEach { file ->
            javaClass.getResourceAsStream("$CONFIG_ROOT/$file").use { stream ->
                if (stream == null) return null
                val parsed = loadSerializedPythonTaintConfig(stream)
                entryPoints.addAll(parsed.entryPoint)
                sources.addAll(parsed.source)
                sinks.addAll(parsed.sink)
                passThroughs.addAll(parsed.passThrough)
                cleaners.addAll(parsed.cleaner)
            }
        }

        return SerializedPythonTaintConfig(
            entryPoint = entryPoints,
            source = sources,
            sink = sinks,
            passThrough = passThroughs,
            cleaner = cleaners,
        )
    }
}
