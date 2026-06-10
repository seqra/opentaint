package org.opentaint.project

import mu.KLogging
import java.nio.file.Path
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.copyTo
import kotlin.io.path.createDirectories
import kotlin.io.path.deleteRecursively
import kotlin.io.path.exists
import kotlin.io.path.forEachDirectoryEntry
import kotlin.io.path.isDirectory
import kotlin.io.path.name
import kotlin.io.path.relativeTo

class PortableProjectCreator(
    private val portableProjectRootPath: Path
) {
    sealed interface PortAction {
        data class Copy(val dst: Path) : PortAction
        data class Ported(val path: Path) : PortAction
    }

    private class ProjectPortContext(
        val sources: Path,
        val classes: Path,
        val dependencies: Path,
        val toolchain: Path,
    ) {
        private var classesCounter = 0
        private var duplicateDependencyCounter = 0
        private var duplicateToolchainCounter = 0

        private val portedDependencies = hashMapOf<String, Path>()
        private val portedToolchain = hashMapOf<String, Path>()

        fun nextClassesPath(suffix: String): Path = classes.resolve("c${classesCounter++}_$suffix")

        fun nextDependencyPath(dependency: Path): PortAction =
            copyWithoutDuplicates(dependency, portedDependencies, dependencies) {
                "d${duplicateDependencyCounter++}"
            }

        fun nextToolchainPath(tc: Path): PortAction =
            copyWithoutDuplicates(tc, portedToolchain, toolchain) {
                "tc${duplicateToolchainCounter++}"
            }

        private inline fun copyWithoutDuplicates(
            path: Path,
            cache: MutableMap<String, Path>,
            newBaseLocation: Path,
            nextDuplicateName: () -> String
        ): PortAction {
            val name = path.name
            val portedPath = cache.putIfAbsent(name, path)

            return when (portedPath) {
                null -> PortAction.Copy(newBaseLocation.resolve(name))
                path -> PortAction.Ported(newBaseLocation.resolve(name))
                else -> PortAction.Copy(
                    newBaseLocation.resolve(nextDuplicateName()).resolve(name)
                )
            }
        }
    }

    fun create(topLevelProject: Project) {
        val portableJava = topLevelProject.javaProjects.mapIndexed { index, project ->
            val projectPath = portableProjectRootPath.resolve("java_$index")
            createJava(project, projectPath) ?: return
        }

        val portableGo = topLevelProject.goProjects.mapIndexed { index, project ->
            val projectPath = portableProjectRootPath.resolve("go_$index")
            createGo(project, projectPath) ?: return
        }

        val portableProject = Project(
            goProjects = portableGo,
            javaProjects = portableJava,
        )

        portableProject.dump(portableProjectRootPath.resolve("project.yaml"))
    }

    fun create(javaOnlyProject: JavaProject) {
        val portableJava = createJava(javaOnlyProject, portableProjectRootPath)
            ?: return

        portableJava.dump(portableProjectRootPath.resolve("project.yaml"))
    }

    private fun createGo(rootProject: GoProject, portableProjectPath: Path): GoProject? {
        logger.info { "Start portable project creation" }

        if (portableProjectPath.exists()) {
            if (!portableProjectPath.isDirectory() || portableProjectPath.isNotEmpty()) {
                logger.warn { "Portable project path exists: overwrite $portableProjectPath" }
                portableProjectPath.cleanupDirectory() ?: return null
            }
        }

        portableProjectPath.createDirectories()

        copy(rootProject.projectDir, portableProjectPath)

        val portableProject = GoProject(portableProjectPath)
        val relativeProject = portableProject.relativeTo(portableProjectRootPath)
        return relativeProject
    }

    private fun createJava(rootProject: JavaProject, portableProjectPath: Path): JavaProject? {
        logger.info { "Start portable project creation" }

        if (portableProjectPath.exists()) {
            if (!portableProjectPath.isDirectory() || portableProjectPath.isNotEmpty()) {
                logger.warn { "Portable project path exists: overwrite $portableProjectPath" }
                portableProjectPath.cleanupDirectory() ?: return null
            }
        }

        portableProjectPath.createDirectories()

        val ctx = ProjectPortContext(
            sources = portableProjectPath.resolve("sources").createDirectories(),
            classes = portableProjectPath.resolve("classes").createDirectories(),
            dependencies = portableProjectPath.resolve("dependencies").createDirectories(),
            toolchain = portableProjectPath.resolve("toolchain").createDirectories()
        )

        rootProject.sourceRoot?.let { copyDirectory(it, ctx.sources) }

        val portableProject = create(ctx, rootProject)
        val relativeProject = portableProject.relativeTo(portableProjectRootPath)
        return relativeProject
    }

    private fun create(ctx: ProjectPortContext, project: JavaProject): JavaProject = JavaProject(
        sourceRoot = project.sourceRoot?.let { copySources(ctx, project, it) },
        javaToolchain = project.javaToolchain?.let { copyToolchain(ctx, it) },
        modules = project.modules.map { create(ctx, project, it) },
        dependencies = project.dependencies.map { copyDependency(ctx, it) },
        subProjects = project.subProjects.map { create(ctx, it) }
    )

    private fun create(ctx: ProjectPortContext, rootProject: JavaProject, module: ProjectModuleClasses) = ProjectModuleClasses(
        packages = module.packages,
        moduleSourceRoot = module.moduleSourceRoot?.let { copySources(ctx, rootProject, it) },
        moduleClasses = module.moduleClasses.map { copyClasses(ctx, it) }
    )

    private fun copySources(ctx: ProjectPortContext, rootProject: JavaProject, source: Path): Path {
        val relativeOriginal = rootProject.sourceRoot?.let { source.relativeTo(it) } ?: source
        return ctx.sources.resolve(relativeOriginal)
    }

    private fun copyClasses(ctx: ProjectPortContext, classes: Path): Path {
        val portedClasses = ctx.nextClassesPath(classes.name)
        copy(classes, portedClasses)
        return portedClasses
    }

    private fun copyDependency(ctx: ProjectPortContext, dependency: Path): Path {
        val portedDependency = ctx.nextDependencyPath(dependency)
        return portedDependency.port(dependency)
    }

    private fun copyToolchain(ctx: ProjectPortContext, toolchain: Path): Path {
        val portedToolchain = ctx.nextToolchainPath(toolchain)
        return portedToolchain.port(toolchain)
    }

    private fun PortAction.port(original: Path): Path = when (this) {
        is PortAction.Ported -> path
        is PortAction.Copy -> {
            copy(original, dst)
            dst
        }
    }

    private fun copy(from: Path, dst: Path) {
        if (from.isDirectory()) {
            copyDirectory(from, dst)
        } else {
            dst.parent?.createDirectories()
            from.copyTo(dst)
        }
    }

    private fun copyDirectory(from: Path, dst: Path) {
        dst.createDirectories()
        from.copyDirRecursivelyTo(dst)
    }

    @OptIn(ExperimentalPathApi::class)
    private fun Path.cleanupDirectory(): Unit? = try {
        deleteRecursively()
    } catch (e: Exception) {
        logger.error("Directory $this cleanup failed", e)
        null
    }

    companion object {
        private val logger = object : KLogging() {}.logger

        private fun Path.isNotEmpty(): Boolean {
            forEachDirectoryEntry { return true }
            return false
        }
    }
}
