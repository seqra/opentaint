package org.opentaint.project

import com.charleskorn.kaml.SingleLineStringStyle
import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.decodeFromStream
import com.charleskorn.kaml.encodeToStream
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import java.nio.file.Path
import java.util.logging.Logger
import kotlin.io.path.Path
import kotlin.io.path.inputStream
import kotlin.io.path.outputStream
import kotlin.io.path.relativeTo

sealed interface CommonProject {
    fun sourceRoot(): Path?
}

@Suppress("DEPRECATION")
@Serializable
data class JavaProject(
    val sourceRoot: @Serializable(with = PathAsStringSerializer::class) Path? = null,
    val javaToolchain: @Serializable(with = PathAsStringSerializer::class) Path? = null,
    val modules: List<ProjectModuleClasses> = emptyList(),
    val dependencies: List<@Serializable(with = PathAsStringSerializer::class) Path> = emptyList(),
    @Deprecated("Use top-level Project.javaProjects instead")
    val subProjects: List<JavaProject> = emptyList(),
): CommonProject {
    override fun sourceRoot(): Path? = sourceRoot

    fun relativeTo(path: Path): JavaProject = JavaProject(
        sourceRoot?.relativeTo(path),
        javaToolchain?.relativeTo(path),
        modules.map { it.relativeTo(path) },
        dependencies.map { it.relativeTo(path) },
        subProjects.map { it.relativeTo(path) }
    )

    fun resolve(base: Path): JavaProject = JavaProject(
        sourceRoot?.let { base.resolve(it) },
        javaToolchain?.let { base.resolve(it) },
        modules.map { it.resolve(base) },
        dependencies.map { base.resolve(it) },
        subProjects.map { it.resolve(base) }
    )

    fun dump(path: Path) {
        path.outputStream().use {
            yaml().encodeToStream(this, it)
        }
    }

    companion object {
        fun load(path: Path): JavaProject = path.inputStream().use {
            yaml().decodeFromStream<JavaProject>(it)
        }
    }
}

@Serializable
data class ProjectModuleClasses(
    val moduleSourceRoot: @Serializable(with = PathAsStringSerializer::class) Path? = null,
    val packages: List<String> = emptyList(),
    val moduleClasses: List<@Serializable(with = PathAsStringSerializer::class) Path> = emptyList()
) {
    fun relativeTo(path: Path): ProjectModuleClasses = ProjectModuleClasses(
        moduleSourceRoot?.relativeTo(path),
        packages,
        moduleClasses.map { it.relativeTo(path) }
    )

    fun resolve(base: Path): ProjectModuleClasses = ProjectModuleClasses(
        moduleSourceRoot?.let { base.resolve(it) },
        packages,
        moduleClasses.map { base.resolve(it) }
    )
}

@Serializable
data class GoProject(
    val projectDir: @Serializable(with = PathAsStringSerializer::class) Path,
): CommonProject {
    override fun sourceRoot(): Path = projectDir

    fun relativeTo(path: Path): GoProject = GoProject(projectDir.relativeTo(path))

    fun resolve(base: Path): GoProject = GoProject(base.resolve(projectDir))
}

@Serializable
data class Project(
    val projectRoot: @Serializable(with = PathAsStringSerializer::class) Path? = null,
    val goProjects: List<GoProject> = emptyList(),
    val javaProjects: List<JavaProject> = emptyList(),
) {
    fun relativeTo(path: Path): Project = Project(
        projectRoot?.relativeTo(path),
        goProjects.map { it.relativeTo(path) },
        javaProjects.map { it.relativeTo(path) },
    )

    fun resolve(base: Path): Project = Project(
        projectRoot?.let { base.resolve(it) },
        goProjects.map { it.resolve(base) },
        javaProjects.map { it.resolve(base) },
    )

    fun dump(path: Path) {
        path.outputStream().use {
            yaml().encodeToStream(this, it)
        }
    }

    companion object {
        private val logger = Logger.getLogger(Project::class.java.name)

        fun load(path: Path): Project = try {
            path.inputStream().use {
                yaml().decodeFromStream<Project>(it)
            }
        } catch (ex: Throwable) {
            logger.warning("Failed to load Project from $path as new format, falling back to legacy JavaProject format: ${ex.message}")
            loadLegacy(path)
        }

        fun loadLegacy(path: Path): Project {
            val root = JavaProject.load(path)
            return Project(
                projectRoot = null,
                goProjects = emptyList(),
                javaProjects = flattenJavaProject(root),
            )
        }

        @Suppress("DEPRECATION")
        fun flattenJavaProject(root: JavaProject): List<JavaProject> {
            val result = mutableListOf<JavaProject>()
            fun visit(p: JavaProject) {
                result += p.copy(subProjects = emptyList())
                p.subProjects.forEach(::visit)
            }
            visit(root)
            return result
        }
    }
}

private fun yaml() = Yaml(
    configuration = YamlConfiguration(
        encodeDefaults = false,
        singleLineStringStyle = SingleLineStringStyle.PlainExceptAmbiguous,
    )
)

object PathAsStringSerializer : KSerializer<Path> {
    override val descriptor = PrimitiveSerialDescriptor("Path", PrimitiveKind.STRING)

    override fun serialize(encoder: Encoder, value: Path) = encoder.encodeString(value.toString())

    override fun deserialize(decoder: Decoder): Path = Path(decoder.decodeString())
}
