package org.opentaint.python.sast.dataflow

// import org.junit.jupiter.api.BeforeAll
// import org.junit.jupiter.api.TestInstance
// import org.opentaint.config.PythonConfigLoader
// import org.opentaint.ir.api.python.PIRClasspath
// import org.opentaint.ir.api.python.PIRSettings
// import org.opentaint.ir.impl.python.PIRClasspathLoader
// import kotlin.io.path.Path
// import kotlin.io.path.absolutePathString
// import kotlin.io.path.createTempDirectory
// import kotlin.io.path.extension
// import kotlin.io.path.isRegularFile
// import kotlin.io.path.walk
// import kotlin.test.Test
//
// @TestInstance(TestInstance.Lifecycle.PER_CLASS)
// class OwaspBenchmarkTest {
//     private lateinit var cp: PIRClasspath
//
//     @BeforeAll
//     fun setup() {
//         val sourcesDir = Path("/home/pvl/folder/projects/explyt/BenchmarkPython")
//
//         val pyFiles = sourcesDir.walk()
//             .filterNot { it.toString().contains(".venv") }
//             .filter { it.isRegularFile() && it.extension == "py" }
//             .mapTo(mutableListOf()) { it.absolutePathString() }
//
// //        val pyFiles = listOf("/home/pvl/folder/projects/explyt/BenchmarkPython/testcode/BenchmarkTest00011.py")
//
//         cp = PIRClasspathLoader(
//             PIRSettings(
//                 sources = pyFiles,
//                 mypyFlags = listOf(
//                     "--ignore-missing-imports",
//                     "--namespace-packages",
//                     "--explicit-package-bases",
//                 ),
//                 searchPaths = listOf(sourcesDir.absolutePathString()),
//                 rpcTimeout = java.time.Duration.ofSeconds(1200),
//             )
//         ).load()
//     }
//
//     @Test
//     fun kek() {
//         PythonConfigLoader.getConfig()
//         println()
//     }
// }
