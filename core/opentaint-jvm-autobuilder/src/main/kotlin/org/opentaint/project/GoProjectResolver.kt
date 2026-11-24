package org.opentaint.project

import java.nio.file.FileVisitResult
import java.nio.file.Path
import kotlin.io.path.visitFileTree

object GoProjectResolver {
    fun resolveProject(root: Path, resolverWorkDir: Path, statuses: MutableList<ProjectStatus>): List<GoProject> {
        val result = mutableListOf<GoProject>()
        val goToolchain by lazy { GoToolchain.resolve(root) }
        root.visitFileTree {
            onPreVisitDirectory { directory, _ ->
                when {
                    directory.isHiddenSubDirOf(root) -> FileVisitResult.SKIP_SUBTREE
                    directory.resolve("go.mod").toFile().exists() -> {
                        result += GoProject(directory, goToolchain.getOrNull())
                        statuses += goToolchain.fold(
                            onSuccess = { ProjectStatus.Built(Language.GO, directory, it) },
                            onFailure = {
                                val error = BuildError(toolchain = null, causes = listOf(it.message.orEmpty()))
                                ProjectStatus.Failed(Language.GO, directory, listOf(error))
                            },
                        )
                        FileVisitResult.SKIP_SUBTREE
                    }
                    else -> FileVisitResult.CONTINUE
                }
            }
        }
        return result
    }
}