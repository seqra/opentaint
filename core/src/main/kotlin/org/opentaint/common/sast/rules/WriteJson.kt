package org.opentaint.common.sast.rules

import kotlinx.serialization.SerializationStrategy
import kotlinx.serialization.json.Json
import mu.KLogging
import java.nio.file.Path
import kotlin.io.path.outputStream

private val logger = object : KLogging() {}.logger

internal fun <T> writeJson(file: Path, serializer: SerializationStrategy<T>, value: T, name: String) {
    runCatching {
        val pretty = Json { prettyPrint = true }
        file.outputStream().bufferedWriter().use { it.write(pretty.encodeToString(serializer, value)) }
        logger.info { "Wrote $name to $file" }
    }.onFailure { logger.error(it) { "Failed to write $name to $file: ${it.message}" } }
}
