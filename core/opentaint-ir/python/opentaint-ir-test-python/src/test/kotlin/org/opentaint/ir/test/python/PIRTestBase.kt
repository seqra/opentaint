package org.opentaint.ir.test.python

import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRClasspathLoader
import java.io.File
import java.nio.file.Files

abstract class PIRTestBase {
    protected fun buildFromSource(
        source: String,
        moduleName: String = "__test__"
    ): PIRClasspath {
        val tmpDir = Files.createTempDirectory("pir-test").toFile()
        tmpDir.deleteOnExit()
        val file = File(tmpDir, "$moduleName.py")
        file.writeText(source.trimIndent())
        file.deleteOnExit()

        return PIRClasspathLoader(PIRSettings(
            sources = listOf(file.absolutePath),
            packageRoots = listOf(tmpDir.absolutePath),
            mypyFlags = listOf("--ignore-missing-imports"),
        )).load()
    }
}
