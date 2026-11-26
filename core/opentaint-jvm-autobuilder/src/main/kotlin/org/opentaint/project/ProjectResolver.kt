package org.opentaint.project

import mu.KLogging
import org.zeroturnaround.exec.ProcessExecutor
import org.zeroturnaround.exec.stream.LogOutputStream
import java.nio.file.FileVisitResult
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.createTempDirectory
import kotlin.io.path.visitFileTree

sealed interface ProjectResolver {
    val projectSourceRoot: Path

    /** Why [resolveProject] returned null. */
    val buildErrors: List<BuildError>

    fun resolveProject(): JavaProject?

    companion object {
        val logger = object : KLogging() {}.logger

        private val JAVA_HOME: String? by lazy { System.getenv("JAVA_HOME") }
        private val JAVA_8_HOME: String? by lazy { System.getenv("JAVA_8_HOME") }
        private val JAVA_11_HOME: String? by lazy { System.getenv("JAVA_11_HOME") }
        private val JAVA_17_HOME: String? by lazy { System.getenv("JAVA_17_HOME") }
        private val JAVA_21_HOME: String? by lazy { System.getenv("JAVA_21_HOME") }
        private val JAVA_LATEST_HOME: String? by lazy { System.getenv("JAVA_LATEST_HOME") }
        private val JAVA_CURRENT_HOME: String? by lazy {
            JavaToolchain.getRunningJvmJavaHome()
        }

        private val availableJavaToolchains: List<JavaToolchain> by lazy {
            listOfNotNull(
                JAVA_HOME, JAVA_8_HOME, JAVA_LATEST_HOME, JAVA_21_HOME,
                JAVA_17_HOME, JAVA_11_HOME, JAVA_CURRENT_HOME
            )
                .map { JavaToolchain.ConcreteJavaToolchain(it) }
                .distinctBy { it.path() }
                .ifEmpty { listOf(JavaToolchain.DefaultJavaToolchain) }
        }

        fun tryJavaToolchains(
            workDir: Path,
            args: List<String>,
            failureCauses: () -> BuildFailureCauses,
            errors: MutableList<BuildError>,
        ): JavaToolchain? {
            for (toolchain in availableJavaToolchains) {
                val causes = failureCauses()
                val exitCode = runCommand(workDir, args, toolchain, causes)
                if (exitCode == 0) return toolchain
                errors += BuildError(toolchain.path(), causes.causes(exitCode))
            }
            return null
        }

        fun resolveProject(rootDir: Path, resolverWorkDir: Path, statuses: MutableList<ProjectStatus>): JavaProject? {
            resolverWorkDir.createDirectories()

            val projectResolvers = mutableListOf<ProjectResolver>()
            rootDir.visitFileTree {
                onPreVisitDirectory { directory, _ ->
                    when {
                        directory.isHiddenSubDirOf(rootDir) -> FileVisitResult.SKIP_SUBTREE

                        GradleProjectResolver.isGradleProjectRoot(directory) -> {
                            logger.info { "Detect gradle project at $directory" }

                            projectResolvers += GradleProjectResolver(
                                resolverDir = createTempDirectory(resolverWorkDir, prefix = "gradle_project_"),
                                projectSourceRoot = directory
                            )

                            FileVisitResult.SKIP_SUBTREE
                        }

                        MavenProjectResolver.isMavenProjectRoot(directory) -> {
                            logger.info { "Detect maven project at $directory" }

                            projectResolvers += MavenProjectResolver(
                                resolverDir = createTempDirectory(resolverWorkDir, prefix = "maven_project_"),
                                projectSourceRoot = directory
                            )

                            FileVisitResult.SKIP_SUBTREE
                        }

                        else -> FileVisitResult.CONTINUE
                    }
                }
            }

            val resolvedProjects = mutableListOf<JavaProject>()
            for (resolver in projectResolvers) {
                val root = resolver.projectSourceRoot
                logger.info { "Start project resolution for: $root" }
                try {
                    val project = resolver.resolveProject()
                    if (project == null) {
                        statuses += ProjectStatus.Failed(Language.JAVA, root, resolver.buildErrors)
                        continue
                    }
                    resolvedProjects += project
                    statuses += ProjectStatus.Built(Language.JAVA, root, project.javaToolchain)
                } catch (ex: Throwable) {
                    logger.error(ex) { "Project resolution failed for: $root" }
                    val error = BuildError(toolchain = null, causes = listOf(ex.toString()))
                    statuses += ProjectStatus.Failed(Language.JAVA, root, resolver.buildErrors + error)
                }
            }

            return when (resolvedProjects.size) {
                0 -> null
                1 -> resolvedProjects.single()

                else -> {
                    // todo: better handling for multiple projects
                    JavaProject(
                        sourceRoot = rootDir,
                        javaToolchain = resolvedProjects.first().javaToolchain,
                        modules = emptyList(),
                        subProjects = resolvedProjects
                    )
                }
            }
        }

        internal fun runCommand(
            workDir: Path,
            args: List<String>,
            javaToolchain: JavaToolchain,
            failureCauses: BuildFailureCauses? = null,
        ): Int =
            ProcessExecutor()
                .command(args)
                .apply {
                    when (javaToolchain) {
                        JavaToolchain.DefaultJavaToolchain -> {}
                        is JavaToolchain.ConcreteJavaToolchain -> {
                            environment("JAVA_HOME", javaToolchain.javaHome)
                        }
                    }
                }
                .directory(workDir.toFile())
                // One stream, so that the failure causes see the lines in the order the tool printed them.
                .redirectErrorStream(true)
                .redirectOutput(object : LogOutputStream() {
                    override fun processLine(line: String) {
                        logger.info { line }
                        failureCauses?.accept(line)
                    }
                })
                .executeNoTimeout().exitValue
    }
}

fun Path.resolve(other: List<String>): Path = other.fold(this) { path, o -> path.resolve(o) }

fun Path.createParentDirectories() = also {
    parent?.createDirectories()
}

fun Path.isHiddenSubDirOf(root: Path): Boolean =
    this != root && fileName?.toString()?.startsWith(".") == true
