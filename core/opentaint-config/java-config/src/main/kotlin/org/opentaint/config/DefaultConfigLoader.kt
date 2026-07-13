package org.opentaint.config

import org.opentaint.dataflow.configuration.ConfigurationLoader
import java.nio.file.FileSystems
import java.nio.file.Files
import java.util.Collections
import kotlin.streams.asSequence

interface DefaultConfigLoader<Rules> {
    val configRoot: String
    val configLoader: ConfigurationLoader<Rules>

    fun loadConfig(): Rules? {
        val resources = javaClass.getResource(configRoot) ?: return null
        val uri = resources.toURI()

        // it is expected to be used as a .jar-dependency
        if (uri.scheme != "jar") return null

        val allFiles =
            FileSystems.newFileSystem(uri, Collections.emptyMap<String, String>()).use { fs ->
                val path = fs.getPath(configRoot)
                Files.walk(path).asSequence().map { path.relativize(it).toString() }.toList()
            }
        if (allFiles.isEmpty()) return null
        val files = allFiles.filter { it.endsWith(".yaml") }

        val loaded = mutableListOf<Rules>()
        files.forEach { file ->
            javaClass.getResourceAsStream("$configRoot/$file").use { str ->
                str?.let { configLoader.load(it) }?.let { loaded.add(it) }
            }
        }

        return configLoader.join(loaded)
    }
}
