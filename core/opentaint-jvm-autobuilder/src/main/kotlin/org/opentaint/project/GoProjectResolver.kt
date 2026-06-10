package org.opentaint.project

import java.nio.file.FileVisitResult
import java.nio.file.Path
import kotlin.io.path.visitFileTree

object GoProjectResolver {
    fun resolveProject(root: Path, resolverWorkDir: Path): List<GoProject> {
        val result = mutableListOf<GoProject>()
        root.visitFileTree {
            onPreVisitDirectory { directory, _ ->
                when {
                    directory.isHiddenSubDirOf(root) -> FileVisitResult.SKIP_SUBTREE
                    directory.resolve("go.mod").toFile().exists() -> {
                        result += GoProject(directory)
                        FileVisitResult.SKIP_SUBTREE
                    }
                    else -> FileVisitResult.CONTINUE
                }
            }
        }
        return result
    }
}