package org.opentaint.ir.test.python.tier1

import org.junit.jupiter.api.Assertions.*
import org.opentaint.ir.api.python.*
import org.opentaint.ir.impl.python.PIRClasspathLoader
import org.opentaint.ir.test.python.PIRTestBase
import java.io.File

abstract class BenchmarkTestBase : PIRTestBase() {

    protected fun analyzePkg(
        pythonModule: String,
        pythonVersion: String,
        expectedModules: Int,
        expectedClasses: Int,
        expectedTopLevelFunctions: Int,
        recursive: Boolean = false,
    ) {
        val pkgDir = findPackageDir(pythonModule)
        val pyFiles = listPyFiles(pkgDir, recursive)
        assertTrue(pyFiles.isNotEmpty(), "No .py files found in $pkgDir")

        var root = File(pkgDir)
        repeat(pythonModule.count { it == '.' } + 1) { root = root.parentFile }

        val cp = createClasspath(pyFiles, root.absolutePath, pythonVersion)
        verifyClasspath(pythonModule, pyFiles.size, cp, expectedModules, expectedClasses, expectedTopLevelFunctions)
    }

    protected fun analyzeDir(
        projectName: String,
        sourceDir: String,
        projectRoot: String,
        pythonVersion: String,
        expectedModules: Int,
        expectedClasses: Int,
        expectedTopLevelFunctions: Int,
    ) {
        val dir = File(sourceDir)
        assertTrue(dir.isDirectory, "Source directory not found: $sourceDir")

        val pyFiles = listSources(dir)

        assertTrue(pyFiles.isNotEmpty(), "No .py files found in $sourceDir")

        val cp = createClasspath(pyFiles, projectRoot, pythonVersion)

        verifyClasspath(projectName, pyFiles.size, cp, expectedModules, expectedClasses, expectedTopLevelFunctions)
    }

    private fun listSources(dir: File): List<String> =
        dir.walk()
            .filter { it.isFile && it.extension == "py" }
            .filter { f ->
                val rel = f.relativeTo(dir).path
                !rel.contains("/test") && !rel.contains("/tests/") &&
                !rel.contains("/migrations/") && !rel.contains("/venv/") &&
                !rel.contains("/.venv/") && !rel.contains("/node_modules/") &&
                !rel.startsWith("test") && !f.name.startsWith("test_") &&
                !f.name.startsWith("conftest")
            }
            .toList()
            .sortedByDescending { if (it.name == "__init__.py") Long.MAX_VALUE else it.length() }
            .map { it.absolutePath }

    private fun createClasspath(
        pyFiles: List<String>,
        projectRoot: String,
        pythonVersion: String,
    ): PIRClasspath {
        return PIRClasspathLoader(PIRSettings(
            sources = pyFiles,
            packageRoots = listOf(projectRoot),
            pythonVersion = pythonVersion,
            mypyFlags = listOf("--ignore-missing-imports"),
            rpcTimeout = java.time.Duration.ofSeconds(1200),
        )).load()
    }

    private fun verifyClasspath(
        name: String,
        fileCount: Int,
        cp: PIRClasspath,
        expectedModules: Int,
        expectedClasses: Int,
        expectedTopLevelFunctions: Int,
    ) {
        cp.use {
            val unknownModules = it.modules.filter { m -> m.isUnknown }
            val knownModules = it.modules.filter { m -> !m.isUnknown }

            val stats = collectStats(knownModules)

            println("╔══════════════════════════════════════════════════════════════")
            println("║ $name ($fileCount files)")
            println("║ Python ${cp.pythonVersion}, mypy ${cp.mypyVersion}")
            println("║ Modules: ${stats.modules} (+ ${unknownModules.size} unknown)")
            println("║ Classes: ${stats.classes} (+ ${stats.syntheticClasses} synthetic)")
            println("║ Top-level functions: ${stats.topLevelFunctions}, all functions: ${stats.functions}")
            println("║ Blocks: ${stats.blocks}, Instructions: ${stats.instructions}")
            println("║ Instruction kinds: ${stats.instructionKinds.size} types")
            println("║ Dangling edges: ${stats.danglingEdges}, Unreachable: ${stats.unreachableBlocks}")
            println("║ Exception handlers: ${stats.blocksWithHandlers}, Errors: ${stats.errorDiagnostics}")
            if (unknownModules.isNotEmpty()) {
                println("║ Unknown modules:")
                unknownModules.forEach { m ->
                    val errs = m.diagnostics.joinToString("; ") { d -> d.message }
                    println("║   ${m.name}: $errs")
                }
            }
            println("╚══════════════════════════════════════════════════════════════")

            assertTrue(unknownModules.isEmpty(),
                "$name: ${unknownModules.size} modules failed to build:\n" +
                    unknownModules.joinToString("\n") { m ->
                        "  ${m.name}: ${m.diagnostics.joinToString("; ") { d -> d.message }}"
                    })

            if (stats.errorDiagnosticMessages.isNotEmpty()) {
                println("║ ERRORS:")
                stats.errorDiagnosticMessages.take(10).forEach { msg -> println("║   $msg") }
            }
            assertEquals(0, stats.errorDiagnostics,
                "$name: found ${stats.errorDiagnostics} loading errors:\n" +
                    stats.errorDiagnosticMessages.take(10).joinToString("\n") { msg -> "  $msg" })

            assertEquals(0, stats.emptyFunctions,
                "$name: ${stats.emptyFunctions} functions with empty CFG:\n  " +
                    stats.emptyFunctionNames.take(20).joinToString("\n  "))

            assertEquals(0, stats.zeroInstructionFunctions,
                "$name: ${stats.zeroInstructionFunctions} functions with 0 instructions:\n  " +
                    stats.zeroInstructionFunctionNames.take(20).joinToString("\n  "))

            assertEquals(fileCount, stats.modules + unknownModules.size,
                "$name: ${fileCount - stats.modules - unknownModules.size} source files silently dropped")

            assertEquals(expectedModules, stats.modules,
                "$name: module count mismatch")
            assertEquals(expectedClasses, stats.classes,
                "$name: class count mismatch")
            assertEquals(expectedTopLevelFunctions, stats.topLevelFunctions,
                "$name: top-level function count mismatch")

            assertEquals(0, stats.danglingEdges,
                "$name: found ${stats.danglingEdges} dangling edges in CFGs")

            assertTrue(stats.instructionKinds.size >= 3,
                "$name: instruction diversity too low — only ${stats.instructionKinds.size} types: " +
                    stats.instructionKinds)

            if (stats.blocks > 0) {
                val pct = stats.unreachableBlocks.toDouble() / stats.blocks
                assertTrue(pct < 0.10,
                    "$name: too many unreachable blocks: ${stats.unreachableBlocks}/${stats.blocks} " +
                        "(${"%.1f".format(pct * 100)}%)")
            }
        }
    }

    data class Stats(
        val modules: Int, val classes: Int, val syntheticClasses: Int,
        val topLevelFunctions: Int, val functions: Int,
        val blocks: Int, val instructions: Int,
        val instructionKinds: Set<String>,
        val danglingEdges: Int,
        val unreachableBlocks: Int,
        val blocksWithHandlers: Int,
        val errorDiagnostics: Int,
        val errorDiagnosticMessages: List<String>,
        val emptyFunctions: Int,
        val emptyFunctionNames: List<String>,
        val zeroInstructionFunctions: Int,
        val zeroInstructionFunctionNames: List<String>,
    )

    private fun collectStats(modules: List<PIRModule>): Stats {
        var moduleCount = 0; var classes = 0; var syntheticClasses = 0
        var topLevelFunctions = 0; var functions = 0
        var blocks = 0; var instructions = 0
        val instructionKinds = mutableSetOf<String>()
        var danglingEdges = 0; var unreachableBlocks = 0; var blocksWithHandlers = 0
        val emptyFunctionNames = mutableListOf<String>()
        val zeroInstructionFunctionNames = mutableListOf<String>()
        val errorMessages = mutableListOf<String>()

        for (module in modules) {
            moduleCount++
            classes += module.classes.count { c -> !isSynthetic(c.name) }
            syntheticClasses += module.classes.count { c -> isSynthetic(c.name) }
            topLevelFunctions += module.functions.count { f -> !isSynthetic(f.name) }
            for (d in module.diagnostics) {
                if (d.severity == PIRDiagnosticSeverity.ERROR) {
                    errorMessages.add("${d.functionName}: ${d.message}")
                }
            }
            for (func in allFunctions(module)) {
                functions++
                val cfg = func.cfg
                blocks += cfg.blocks.size
                if (cfg.blocks.isEmpty()) {
                    emptyFunctionNames.add(func.qualifiedName)
                } else if (cfg.blocks.sumOf { b -> b.instructions.size } == 0) {
                    zeroInstructionFunctionNames.add(func.qualifiedName)
                }
                val allLabels = cfg.blocks.map { it.label }.toSet()
                for (block in cfg.blocks) {
                    instructions += block.instructions.size
                    if (block.exceptionHandlers.isNotEmpty()) blocksWithHandlers++
                    for (inst in block.instructions) {
                        instructionKinds.add(inst::class.simpleName ?: "Unknown")
                        when (inst) {
                            is PIRGoto -> if (inst.targetBlock !in allLabels) danglingEdges++
                            is PIRBranch -> {
                                if (inst.trueBlock !in allLabels) danglingEdges++
                                if (inst.falseBlock !in allLabels) danglingEdges++
                            }
                            is PIRNextIter -> {
                                if (inst.bodyBlock !in allLabels) danglingEdges++
                                if (inst.exitBlock !in allLabels) danglingEdges++
                            }
                            else -> {}
                        }
                    }
                    for (h in block.exceptionHandlers) {
                        if (h !in allLabels) danglingEdges++
                    }
                }
                if (cfg.blocks.isNotEmpty()) {
                    val reachable = mutableSetOf(cfg.entryBlock.label)
                    val queue = ArrayDeque<PIRBasicBlock>()
                    queue.add(cfg.entryBlock)
                    while (queue.isNotEmpty()) {
                        val b = queue.removeFirst()
                        for (succ in cfg.successors(b) + cfg.exceptionalSuccessors(b)) {
                            if (succ.label !in reachable) {
                                reachable.add(succ.label)
                                queue.add(succ)
                            }
                        }
                    }
                    unreachableBlocks += cfg.blocks.size - reachable.size
                }
            }
        }
        return Stats(
            moduleCount, classes, syntheticClasses, topLevelFunctions, functions,
            blocks, instructions,
            instructionKinds, danglingEdges, unreachableBlocks, blocksWithHandlers,
            errorMessages.size, errorMessages,
            emptyFunctionNames.size, emptyFunctionNames,
            zeroInstructionFunctionNames.size, zeroInstructionFunctionNames,
        )
    }

    private fun allFunctions(module: PIRModule): Sequence<PIRFunction> = sequence {
        yield(module.moduleInit)
        yieldAll(module.functions)
        for (cls in module.classes) yieldAll(classFunctions(cls))
    }

    private fun classFunctions(cls: PIRClass): Sequence<PIRFunction> = sequence {
        yieldAll(cls.methods)
        for (nested in cls.nestedClasses) yieldAll(classFunctions(nested))
    }

    private fun isSynthetic(name: String): Boolean =
        name.contains('$') || name.contains('<') || name.contains('>')

    companion object {
        fun findPackageDir(pythonModule: String): String {
            val proc = ProcessBuilder(
                System.getenv("PIR_SERVER_PYTHON") ?: error("PIR_SERVER_PYTHON is not set"), "-c",
                "import $pythonModule, os; print(os.path.dirname($pythonModule.__file__))"
            ).redirectErrorStream(true).start()
            val output = proc.inputStream.bufferedReader().readText().trim()
            proc.waitFor()
            if (proc.exitValue() != 0) {
                throw IllegalStateException("Cannot locate package $pythonModule: $output")
            }
            return output
        }

        fun listPyFiles(dir: String, recursive: Boolean = false): List<String> {
            val allFiles = if (recursive) {
                File(dir).walk()
                    .filter { it.isFile && it.extension == "py" }
                    .toList()
                    .sortedByDescending { if (it.name == "__init__.py") Long.MAX_VALUE else it.length() }
            } else {
                File(dir).listFiles()
                    ?.filter { it.extension == "py" && it.isFile }
                    ?.sortedByDescending { if (it.name == "__init__.py") Long.MAX_VALUE else it.length() }
                    ?: emptyList()
            }
            return allFiles.map { it.absolutePath }
        }
    }
}
