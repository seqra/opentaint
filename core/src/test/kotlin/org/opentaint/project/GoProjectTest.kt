package org.opentaint.project

import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.createFile
import kotlin.io.path.readText
import kotlin.io.path.writeText
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull

class GoProjectTest {
    private val tmp: Path = Files.createTempDirectory("go-project-test")

    @Test
    fun `go toolchain survives dump and load`() {
        val file = tmp.resolve("project.yaml")
        val toolchain = tmp.resolve("goroot").toAbsolutePath()

        Project(goProjects = listOf(GoProject(Path("go_0"), toolchain))).dump(file)

        assertEquals(listOf(GoProject(Path("go_0"), toolchain)), Project.load(file).goProjects)
    }

    @Test
    fun `project without go toolchain has no such field`() {
        val file = tmp.resolve("project.yaml")

        Project(goProjects = listOf(GoProject(Path("go_0")))).dump(file)

        assertFalse("goToolchain" in file.readText())
        assertNull(Project.load(file).goProjects.single().goToolchain)
    }

    @Test
    fun `project model written before the field loads without go toolchain`() {
        val file = tmp.resolve("project.yaml")
        file.writeText("goProjects:\n- projectDir: go_0\n")

        assertEquals(listOf(GoProject(Path("go_0"))), Project.load(file).goProjects)
    }

    @Test
    fun `go toolchain stays absolute in a portable model`() {
        val toolchain = tmp.resolve("goroot").toAbsolutePath()
        val project = GoProject(tmp.resolve("model").resolve("go_0"), toolchain)

        val portable = project.relativeTo(tmp.resolve("model"))
        assertEquals(GoProject(Path("go_0"), toolchain), portable)

        val resolved = portable.resolve(tmp.resolve("other"))
        assertEquals(GoProject(tmp.resolve("other").resolve("go_0"), toolchain), resolved)
    }

    @Test
    fun `go executable is the go binary of the toolchain`() {
        val toolchain = tmp.resolve("goroot")
        assertNull(GoProject(tmp).goExecutable())
        assertNull(GoProject(tmp, toolchain).goExecutable())

        val go = toolchain.resolve("bin").createDirectories().resolve("go").createFile()
        assertEquals(go, GoProject(tmp, toolchain).goExecutable())
    }
}
