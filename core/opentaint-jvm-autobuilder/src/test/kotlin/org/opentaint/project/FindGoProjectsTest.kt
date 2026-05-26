package org.opentaint.project

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.io.TempDir
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.writeText
import kotlin.test.assertEquals

class FindGoProjectsTest {
    @Test
    fun `detects top-level go mod`(@TempDir root: Path) {
        (root.resolve("go.mod")).writeText("module example.com/main\n")
        val result = findGoProjectsForTest(root)
        assertEquals(listOf(root), result.map { it.projectDir })
    }

    @Test
    fun `stops descent at nested go mod`(@TempDir root: Path) {
        (root.resolve("go.mod")).writeText("module example.com/main\n")
        val sub = root.resolve("sub").createDirectories()
        (sub.resolve("go.mod")).writeText("module example.com/sub\n")
        val result = findGoProjectsForTest(root)
        assertEquals(listOf(root), result.map { it.projectDir })
    }

    @Test
    fun `picks up sibling Go modules under a non-Go parent`(@TempDir root: Path) {
        val a = root.resolve("a").createDirectories().also { (it.resolve("go.mod")).writeText("module a\n") }
        val b = root.resolve("b").createDirectories().also { (it.resolve("go.mod")).writeText("module b\n") }
        val result = findGoProjectsForTest(root).map { it.projectDir }.sortedBy { it.fileName.toString() }
        assertEquals(listOf(a, b), result)
    }
}

internal fun findGoProjectsForTest(root: Path): List<GoProject> = findGoProjects(root)
