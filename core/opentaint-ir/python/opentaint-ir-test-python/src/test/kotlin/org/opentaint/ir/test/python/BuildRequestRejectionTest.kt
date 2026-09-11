package org.opentaint.ir.test.python

import org.junit.jupiter.api.Test
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRBuildException
import org.opentaint.ir.impl.python.PIRClasspathLoader
import java.io.File
import java.nio.file.Files
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class BuildRequestRejectionTest {

    @Test
    fun `an unrecognized mypy flag is rejected`() =
        assertRejected("--no-such-mypy-flag", mypyFlags = listOf("--no-such-mypy-flag"))

    @Test
    fun `a python_version above the server interpreter is rejected`() =
        assertRejected("3.99", pythonVersion = "3.99")

    @Test
    fun `a malformed python_version is rejected`() =
        assertRejected("not-a-version", pythonVersion = "not-a-version")

    @Test
    fun `a package root inside a package is rejected`() =
        assertRejected("is inside package 'pkg'", sourceDir = ::packageDirInside)

    @Test
    fun `a directory source is rejected`() =
        assertRejected("is a directory", sources = { listOf(it.parentFile.absolutePath) })

    @Test
    fun `a nonexistent source is rejected`() =
        assertRejected("no such file", sources = { listOf(File(it.parentFile, "absent.py").absolutePath) })

    @Test
    fun `a non-Python source is rejected`() =
        assertRejected("not a Python source", sources = { listOf(nonPythonSibling(it).absolutePath) })

    @Test
    fun `the same module provided twice is rejected`() =
        assertRejected("duplicates module", sources = { listOf(it.absolutePath, it.absolutePath) })

    @Test
    fun `a source under a package dir with an invalid name is rejected`() =
        assertRejected("not a valid Python package name", sources = { listOf(inBadlyNamedPackage(it).absolutePath) })

    private fun inBadlyNamedPackage(sample: File): File {
        val pkg = File(sample.parentFile, "bad-name").apply { mkdir(); deleteOnExit() }
        File(pkg, "__init__.py").apply { writeText(""); deleteOnExit() }
        return File(pkg, "mod.py").apply { writeText("def f(): pass\n"); deleteOnExit() }
    }

    private fun nonPythonSibling(sample: File): File =
        File(sample.parentFile, "notes.txt").apply {
            writeText("not python\n")
            deleteOnExit()
        }

    private fun packageDirInside(root: File): File =
        File(root, "pkg").apply {
            mkdir()
            deleteOnExit()
            File(this, "__init__.py").apply { writeText(""); deleteOnExit() }
        }

    private fun assertRejected(
        expectedInMessage: String,
        mypyFlags: List<String> = listOf("--ignore-missing-imports"),
        pythonVersion: String? = null,
        sourceDir: (File) -> File = { it },
        sources: (File) -> List<String> = { listOf(it.absolutePath) },
    ) {
        val root = Files.createTempDirectory("build-rejection-test").toFile()
        root.deleteOnExit()

        val dir = sourceDir(root)
        val source = File(dir, "sample.py")
        source.writeText("def handler(): pass\n")
        source.deleteOnExit()

        val error = assertFailsWith<PIRBuildException> {
            PIRClasspathLoader(
                PIRSettings(
                    sources = sources(source),
                    packageRoots = listOf(dir.absolutePath),
                    pythonVersion = pythonVersion,
                    mypyFlags = mypyFlags,
                ),
            ).load()
        }

        assertTrue(
            error.message.orEmpty().contains(expectedInMessage),
            "Expected '$expectedInMessage' in the rejection, got: ${error.message}",
        )
    }
}
