package org.opentaint.project

import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.readText
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse

class GoProjectTest {
    private val tmp: Path = Files.createTempDirectory("go-project-test")
    private val file = tmp.resolve("project.yaml")
    private val toolchain = tmp.resolve("goroot").toAbsolutePath()

    @Test
    fun `go toolchain survives dump and load`() {
        Project(goProjects = listOf(GoProject(Path("go_0"), toolchain))).dump(file)

        assertEquals(listOf(GoProject(Path("go_0"), toolchain)), Project.load(file).goProjects)
    }

    @Test
    fun `project without go toolchain has no such field`() {
        Project(goProjects = listOf(GoProject(Path("go_0")))).dump(file)

        assertFalse("goToolchain" in file.readText())
        assertEquals(listOf(GoProject(Path("go_0"))), Project.load(file).goProjects)
    }

    @Test
    fun `go toolchain stays absolute in a portable model`() {
        val project = GoProject(tmp.resolve("model").resolve("go_0"), toolchain)

        val portable = project.relativeTo(tmp.resolve("model"))
        assertEquals(GoProject(Path("go_0"), toolchain), portable)

        val resolved = portable.resolve(tmp.resolve("other"))
        assertEquals(GoProject(tmp.resolve("other").resolve("go_0"), toolchain), resolved)
    }
}
