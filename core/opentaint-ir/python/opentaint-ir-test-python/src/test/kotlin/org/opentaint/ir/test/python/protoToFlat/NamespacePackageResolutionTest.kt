package org.opentaint.ir.test.python.protoToFlat

import org.junit.jupiter.api.Test
import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.flat.FlatCall
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import java.io.File
import java.nio.file.Files
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class NamespacePackageResolutionTest {

    private data class Fixture(val mainPath: String, val helperPath: String, val rootDir: String)

    private data class SplitFixture(val mainPath: String, val appDir: String, val libDir: String)

    private fun writeHelper(dir: File): File {
        val dbSqlite = File(dir, "db_sqlite.py")
        dbSqlite.writeText(
            """
                def run_query(q):
                    return q
            """.trimIndent(),
        )
        dbSqlite.deleteOnExit()
        return dbSqlite
    }

    private fun writeMain(dir: File): File {
        val main = File(dir, "main.py")
        main.writeText(
            """
                import helpers.db_sqlite

                def f(x):
                    return helpers.db_sqlite.run_query(x)
            """.trimIndent(),
        )
        main.deleteOnExit()
        return main
    }

    private fun makeFixture(): Fixture {
        val tmpDir = Files.createTempDirectory("ns-pkg-test").toFile()
        tmpDir.deleteOnExit()

        val helpersDir = File(tmpDir, "helpers")
        helpersDir.mkdir()
        helpersDir.deleteOnExit()

        val dbSqlite = writeHelper(helpersDir)
        val main = writeMain(tmpDir)

        return Fixture(main.absolutePath, dbSqlite.absolutePath, tmpDir.absolutePath)
    }

    private fun makeSplitFixture(): SplitFixture {
        val tmpDir = Files.createTempDirectory("ns-pkg-split-test").toFile()
        tmpDir.deleteOnExit()

        val appDir = File(tmpDir, "app")
        appDir.mkdir()
        appDir.deleteOnExit()

        val libDir = File(tmpDir, "lib")
        libDir.mkdir()
        libDir.deleteOnExit()

        val helpersDir = File(libDir, "helpers")
        helpersDir.mkdir()
        helpersDir.deleteOnExit()

        writeHelper(helpersDir)
        val main = writeMain(appDir)

        return SplitFixture(main.absolutePath, appDir.absolutePath, libDir.absolutePath)
    }

    private fun resolvedCalleeOfRunQueryIn(fn: FlatFunctionIR): String? {
        for (block in fn.cfg.blocks) {
            for (inst in block.instructions) {
                if (inst is FlatCall) {
                    val resolved = inst.resolvedCallee ?: continue
                    if (resolved.endsWith("run_query")) return resolved
                }
            }
        }
        return null
    }

    private fun loadMain(settings: PIRSettings): FlatFunctionIR {
        val modules = PIRRawFlatLoader.loadRawFlatModules(settings)
        val mainModule: FlatModuleIR = modules.first { it.moduleName == "main" }
        return mainModule.functions.first { it.qualifiedName.endsWith(".f") }
    }

    @Test
    fun `namespace package call resolves through packageRoots`() {
        val fx = makeFixture()

        val f = loadMain(
            PIRSettings(
                sources = listOf(fx.mainPath),
                packageRoots = listOf(fx.rootDir),
                mypyFlags = listOf("--ignore-missing-imports"),
            ),
        )

        val resolved = resolvedCalleeOfRunQueryIn(f)
        assertNotNull(
            resolved,
            "Expected mypy to resolve helpers.db_sqlite.run_query when the package root " +
                "is declared, but FlatCall.resolvedCallee was null.",
        )
        assertTrue(
            resolved.contains("helpers.db_sqlite") && resolved.endsWith("run_query"),
            "Expected resolvedCallee to point into helpers.db_sqlite, got: $resolved",
        )
    }

    @Test
    fun `out of tree namespace package is unresolved when its root is not declared`() {
        val fx = makeSplitFixture()

        val f = loadMain(
            PIRSettings(
                sources = listOf(fx.mainPath),
                packageRoots = listOf(fx.appDir),
                mypyFlags = listOf("--ignore-missing-imports"),
            ),
        )

        assertNull(
            resolvedCalleeOfRunQueryIn(f),
            "helpers/ lives outside every declared package root, so mypy should not be " +
                "able to resolve helpers.db_sqlite.run_query — expected resolvedCallee to be null.",
        )
    }

    @Test
    fun `out of tree namespace package resolves once its root is declared`() {
        val fx = makeSplitFixture()

        val f = loadMain(
            PIRSettings(
                sources = listOf(fx.mainPath),
                packageRoots = listOf(fx.appDir, fx.libDir),
                mypyFlags = listOf("--ignore-missing-imports"),
            ),
        )

        val resolved = resolvedCalleeOfRunQueryIn(f)
        assertNotNull(
            resolved,
            "Declaring the lib root should make helpers.db_sqlite.run_query resolvable, " +
                "but FlatCall.resolvedCallee was null.",
        )
        assertTrue(
            resolved.contains("helpers.db_sqlite") && resolved.endsWith("run_query"),
            "Expected resolvedCallee to point into helpers.db_sqlite, got: $resolved",
        )
    }

    @Test
    fun `namespace package call is unresolved with namespace packages disabled`() {
        val fx = makeFixture()

        val f = loadMain(
            PIRSettings(
                sources = listOf(fx.mainPath),
                packageRoots = listOf(fx.rootDir),
                mypyFlags = listOf("--ignore-missing-imports", "--no-namespace-packages"),
            ),
        )

        assertNull(
            resolvedCalleeOfRunQueryIn(f),
            "With --no-namespace-packages, mypy should not treat helpers/ as a " +
                "PEP 420 package — expected resolvedCallee to be null.",
        )
    }
}
