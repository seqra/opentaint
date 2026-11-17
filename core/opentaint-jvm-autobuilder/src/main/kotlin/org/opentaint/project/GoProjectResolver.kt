package org.opentaint.project

import java.nio.file.FileVisitResult
import java.nio.file.Path
import kotlin.io.path.visitFileTree

object GoProjectResolver {
    fun resolveProject(root: Path, resolverWorkDir: Path): List<GoProject> {
        val result = mutableListOf<GoProject>()
        // One Go installation serves every module: resolve it on the first go.mod.
        val goToolchain by lazy { GoToolchain.resolve(root) }
        root.visitFileTree {
            onPreVisitDirectory { directory, _ ->
                when {
                    directory.isHiddenSubDirOf(root) -> FileVisitResult.SKIP_SUBTREE
                    directory.resolve("go.mod").toFile().exists() -> {
                        result += GoProject(directory, goToolchain)
                        FileVisitResult.SKIP_SUBTREE
                    }
                    else -> FileVisitResult.CONTINUE
                }
            }
        }
        return result
    }
}