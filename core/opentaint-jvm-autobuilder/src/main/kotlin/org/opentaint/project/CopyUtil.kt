package org.opentaint.project

import mu.KLogging
import java.nio.file.FileAlreadyExistsException
import java.nio.file.Files
import java.nio.file.LinkOption
import java.nio.file.Path
import kotlin.io.path.CopyActionResult
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.OnErrorResult
import kotlin.io.path.copyToRecursively
import kotlin.io.path.createDirectory
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
        if (src.isDirectory(LinkOption.NOFOLLOW_LINKS)) {
            createDirectoryIgnoringExisting(dst)
            CopyActionResult.CONTINUE
        } else {
            src.copyToIgnoringExistingDirectory(dst, followLinks = false)
        }
    }
}

// Create a directory explicitly instead of copying it from the source. Copying would propagate the
// source's attributes, and a read-only source (e.g. a JDK from the Nix store) lacks the owner write
// bit, which then makes its child files fail to copy with AccessDeniedException. Mirrors the
// "ignore existing directory" semantics of copyToIgnoringExistingDirectory.
private fun createDirectoryIgnoringExisting(dst: Path) {
    when {
        !dst.exists(LinkOption.NOFOLLOW_LINKS) -> dst.createDirectory()
        !dst.isDirectory(LinkOption.NOFOLLOW_LINKS) -> throw FileAlreadyExistsException(dst.toString())
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
