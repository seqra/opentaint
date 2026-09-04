package org.opentaint.ir.test.python.protoToFlat

import org.junit.jupiter.api.Test
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
import java.io.File
import java.nio.file.Files
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class ModuleNamingTest {

    private fun write(dir: File, name: String, text: String): File {
        val file = File(dir, name)
        file.writeText(text.trimIndent())
        file.deleteOnExit()
        return file
    }

    private fun mkdir(parent: File, name: String): File {
        val dir = File(parent, name)
        dir.mkdirs()
        dir.deleteOnExit()
        return dir
    }

    private fun tmpRoot(prefix: String): File {
        val dir = Files.createTempDirectory(prefix).toFile()
        dir.deleteOnExit()
        return dir
    }

    private fun moduleNames(settings: PIRSettings): Set<String> =
        PIRRawFlatLoader.loadRawFlatModules(settings).map { it.moduleName }.toSet()

    @Test
    fun `each declared root names the files below it`() {
        val root = tmpRoot("multi-root-test")
        val src = mkdir(root, "src")
        val pkg = mkdir(src, "pkg")
        val scripts = mkdir(root, "scripts")

        write(pkg, "__init__.py", "")
        val views = write(pkg, "views.py", "def handler(): pass")
        val tool = write(scripts, "tool.py", "import sys")

        val names = moduleNames(
            PIRSettings(
                sources = listOf(views.absolutePath, tool.absolutePath),
                packageRoots = listOf(src.absolutePath, root.absolutePath),
                mypyFlags = listOf("--ignore-missing-imports"),
            ),
        )

        assertTrue("pkg.views" in names, "Expected pkg.views, got: $names")
        assertTrue("scripts.tool" in names, "Expected scripts.tool, got: $names")
    }

    @Test
    fun `a package root inside a package is rejected`() {
        val root = tmpRoot("root-in-pkg-test")
        val pkg = mkdir(root, "pkg")
        write(pkg, "__init__.py", "")
        val views = write(pkg, "views.py", "def handler(): pass")

        val cp = PIRClasspathLoader(
            PIRSettings(
                sources = listOf(views.absolutePath),
                packageRoots = listOf(pkg.absolutePath),
                mypyFlags = listOf("--ignore-missing-imports"),
            ),
        ).load()

        cp.let {
            assertEquals(listOf("__build_errors__"), it.modules.map { m -> m.name })
            val messages = it.modules.flatMap { m -> m.diagnostics }.map { d -> d.message }
            assertTrue(
                messages.any { msg -> msg.contains("is inside package 'pkg'") },
                "Expected a rejection naming the enclosing package, got: $messages",
            )
        }
    }

    @Test
    fun `implementation file is serialized rather than its stub`() {
        val root = tmpRoot("stub-test")
        val pkg = mkdir(root, "pkg")
        write(pkg, "__init__.py", "")
        write(pkg, "mod.pyi", "def f(x: int) -> int: ...")
        val impl = write(
            pkg,
            "mod.py",
            """
                def f(x):
                    return x

                def only_in_impl():
                    return 1
            """,
        )

        val modules = PIRRawFlatLoader.loadRawFlatModules(
            PIRSettings(
                sources = listOf(impl.absolutePath),
                packageRoots = listOf(root.absolutePath),
                mypyFlags = listOf("--ignore-missing-imports"),
            ),
        )

        val mod = modules.first { it.moduleName == "pkg.mod" }
        assertTrue(
            mod.functions.any { it.qualifiedName.endsWith("only_in_impl") },
            "Expected pkg.mod to come from mod.py, got functions: " +
                mod.functions.map { it.qualifiedName },
        )
    }
}
