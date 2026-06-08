package org.opentaint.project

import mu.KLogging
import java.nio.file.Files
import java.nio.file.LinkOption
import java.nio.file.Path
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.OnErrorResult
import kotlin.io.path.copyToRecursively
import kotlin.io.path.deleteRecursively
import kotlin.io.path.exists
import kotlin.io.path.isDirectory
import kotlin.io.path.isSameFileAs
import kotlin.io.path.isSymbolicLink

private val logger = object : KLogging() {}.logger

@OptIn(ExperimentalPathApi::class)
fun Path.copyDirRecursivelyTo(dst: Path) {
    logger.info { "Copy $this to $dst" }

    if (!copyTargetIsSubdirectory(dst)) {
        copyDirRecursively(this, dst)
        return
    }

    val tmpDir = Files.createTempDirectory("opentaint_tmp")
    try {
        copyDirRecursively(this, tmpDir)
        copyDirRecursively(tmpDir, dst)
    } finally {
        tmpDir.deleteRecursively()
    }
}

@OptIn(ExperimentalPathApi::class)
private fun copyDirRecursively(from: Path, to: Path) {
    from.copyToRecursively(
        to,
        onError = { src, _, ex ->
            logger.error(ex) { "Failed to copy $src" }
            OnErrorResult.SKIP_SUBTREE
        },
        followLinks = false,
    ) { src, dst ->
        val result = src.copyToIgnoringExistingDirectory(dst, followLinks = false)
        // The source may be a read-only JDK (e.g. from the Nix store); a directory copied from it
        // lacks the owner write bit, so its files then fail to copy with AccessDeniedException.
        // Restore it on each copied directory before its children are visited.
        if (dst.isDirectory(LinkOption.NOFOLLOW_LINKS)) {
            dst.toFile().setWritable(true, true)
        }
        result
    }
}

private fun Path.copyTargetIsSubdirectory(target: Path): Boolean {
    if (!this.exists() || this.isSymbolicLink()) return false

    val targetExistsAndNotSymlink = target.exists() && !target.isSymbolicLink()
    if (targetExistsAndNotSymlink && this.isSameFileAs(target)) return false

    return when {
        this.fileSystem != target.fileSystem -> false
        targetExistsAndNotSymlink -> target.toRealPath().startsWith(this.toRealPath())
        else -> target.parent?.let { it.exists() && it.toRealPath().startsWith(this.toRealPath()) } ?: false
    }
}
