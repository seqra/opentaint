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
                    sources = listOf(source.absolutePath),
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
