@file:UseSerializers(PathAsStringSerializer::class)

package org.opentaint.project

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.UseSerializers
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonContentPolymorphicSerializer
import kotlinx.serialization.json.JsonElement
import kotlinx.serialization.json.jsonObject
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.writeText

@Serializable
data class BuildStatus(val projects: List<ProjectStatus>) {
    fun write(dir: Path) {
        dir.createDirectories().resolve(FILE_NAME).writeText(json.encodeToString(this))
    }

    companion object {
        const val FILE_NAME = "status.json"

        private val json = Json { prettyPrint = true }
    }
}

@Serializable
enum class Language {
    @SerialName("java") JAVA,
    @SerialName("go") GO,
}

@Serializable(with = ProjectStatusSerializer::class)
sealed interface ProjectStatus {
    /** Will be analyzed; [toolchain] is the one it was built with. */
    @Serializable
    data class Built(val language: Language, val project: Path, val toolchain: Path?) : ProjectStatus

    /** Will not be analyzed. */
    @Serializable
    data class Failed(val language: Language, val project: Path, val errors: List<BuildError>) : ProjectStatus
}

@Serializable
data class BuildError(val toolchain: Path?, val causes: List<String>)

private object ProjectStatusSerializer : JsonContentPolymorphicSerializer<ProjectStatus>(ProjectStatus::class) {
    override fun selectDeserializer(element: JsonElement) =
        if ("errors" in element.jsonObject) ProjectStatus.Failed.serializer() else ProjectStatus.Built.serializer()
}
