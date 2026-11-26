package org.opentaint.common.sast.rules

import com.charleskorn.kaml.YamlException
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.parseToYamlNode
import kotlinx.serialization.Serializable
import mu.KLogging
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.dataflow.configuration.ConfigurationLoader
import java.nio.file.Path
import kotlin.io.path.absolutePathString
import kotlin.io.path.exists
import kotlin.io.path.readText

private val logger = object : KLogging() {}.logger

class PassThroughModels(private val configs: Map<String, List<Any?>>) {
    @Suppress("UNCHECKED_CAST")
    fun <Rules> of(loader: ConfigurationLoader<Rules>): List<Rules> =
        configs[loader.language].orEmpty() as List<Rules>
}

@Serializable
data class PassThroughModelLoadReport(val files: List<File>) {
    @Serializable
    data class File(
        val path: String,
        val language: String? = null,
        val models: Int,
        val error: Error? = null,
        val warnings: List<String> = emptyList(),
    )

    @Serializable
    data class Error(
        val message: String,
        val line: Int? = null,
        val column: Int? = null,
        val path: String? = null,
    )
}

fun CommonAnalysisOptions.loadPassThroughModels(
    loaders: List<ConfigurationLoader<*>>,
    projectLanguages: Set<String>,
): PassThroughModels {
    val configs = linkedMapOf<String, MutableList<Any?>>()
    val files = customApproximationConfig.map { path ->
        loadModelFile(path, loaders, projectLanguages) { language, config ->
            configs.getOrPut(language) { mutableListOf() } += config
        }.also { it.log() }
    }

    if (files.isNotEmpty()) {
        logger.info {
            "Loaded ${files.sumOf { it.models }} custom pass-through models " +
                "from ${files.size} files (${files.count { it.error != null }} with errors)"
        }
    }
    passthroughApproximationLoadReport?.let {
        writeJson(it, PassThroughModelLoadReport.serializer(), PassThroughModelLoadReport(files), "pass-through model load report")
    }
    return PassThroughModels(configs)
}

private fun loadModelFile(
    path: Path,
    loaders: List<ConfigurationLoader<*>>,
    projectLanguages: Set<String>,
    addConfig: (String, Any?) -> Unit,
): PassThroughModelLoadReport.File {
    val file = PassThroughModelLoadReport.File(path.absolutePathString(), models = 0)
    if (!path.exists()) return file.copy(error = PassThroughModelLoadReport.Error("does not exist"))

    var language: String? = null
    return try {
        val root = ConfigurationLoader.yaml.parseToYamlNode(path.readText()) as? YamlMap
            ?: return file.copy(warnings = listOf("root is not a map"))
        language = root.getScalar("language")?.content
            ?: return file.copy(warnings = listOf("no language"))
        val loader = loaders.find { it.language == language }
            ?: return file.copy(language = language, warnings = listOf("language $language is not supported"))
        if (language !in projectLanguages) return file.copy(language = language)

        val loaded = loader.loadModels(root)
        addConfig(language, loaded.config)
        file.copy(language = language, models = loaded.count, warnings = root.ignoredSections() + loaded.warnings)
    } catch (e: Exception) {
        file.copy(language = language, error = e.toLoadError())
    }
}

private fun YamlMap.ignoredSections(): List<String> {
    val ignored = entries.keys.map { it.content } - setOf("language", "passThrough")
    if (ignored.isEmpty()) return emptyList()
    return listOf("sections other than passThrough are ignored: ${ignored.joinToString()}")
}

private fun Exception.toLoadError() = when (this) {
    is YamlException -> with(innermost()) {
        PassThroughModelLoadReport.Error(message, line, column, path.toHumanReadableString())
    }
    else -> PassThroughModelLoadReport.Error(message ?: toString())
}

private tailrec fun YamlException.innermost(): YamlException {
    val cause = cause as? YamlException ?: return this
    return cause.innermost()
}

private fun PassThroughModelLoadReport.File.log() {
    error?.let { logger.warn { "Skip pass-through model file $path: ${it.message}" } }
    warnings.forEach { logger.warn { "Pass-through model file $path: $it" } }
}
