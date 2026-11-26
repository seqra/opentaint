package org.opentaint.common.sast

import kotlinx.serialization.json.Json
import org.opentaint.common.sast.rules.PassThroughModelLoadReport
import org.opentaint.common.sast.rules.PassThroughModels
import org.opentaint.common.sast.rules.loadPassThroughModels
import org.opentaint.dataflow.configuration.go.serialized.GoConfigurationLoader
import org.opentaint.dataflow.configuration.jvm.serialized.JavaConfigurationLoader
import org.opentaint.go.sast.project.GoProjectAnalysisOptions
import org.opentaint.jvm.sast.project.ProjectAnalysisOptions
import org.opentaint.project.GoProject
import org.opentaint.project.JavaProject
import org.opentaint.project.Project
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.readText
import kotlin.io.path.writeText
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class PassThroughModelLoadTest {
    private val tmp: Path = Files.createTempDirectory("pass-through-model-load-test")
    private val reportFile = tmp.resolve("report.json")
    private val javaLoader = JavaConfigurationLoader()
    private val goLoader = GoConfigurationLoader()

    private val javaModels = """
        language: java
        passThrough:
        - function: com.foo.Wrapper#wrap
          copy:
          - from: arg(0)
            to: result
        - function: com.foo.Wrapper#unwrap
          copy:
          - from: this
            to: result
    """.trimIndent()

    private val goModels = """
        language: go
        passThrough:
        - function:
            package: github.com/acme/lib
            type: Store
            name: Get
            receiver: true
          copy:
          - from: this
            to: result(0)
        - function:
            name: Decode
          copy:
          - from: arg(0)
            to: result
        - function:
            package: github.com/acme/lib
            name: Split
    """.trimIndent()

    private fun file(name: String, text: String): Path = tmp.resolve(name).also { it.writeText(text) }

    private fun load(vararg files: Path, languages: Set<String> = setOf("java")): PassThroughModels =
        CommonAnalysisOptions(customApproximationConfig = files.toList(), passthroughApproximationLoadReport = reportFile)
            .loadPassThroughModels(listOf(javaLoader, goLoader), languages)

    private fun report(): List<PassThroughModelLoadReport.File> =
        Json.decodeFromString<PassThroughModelLoadReport>(reportFile.readText()).files

    private fun loadOne(text: String, languages: Set<String> = setOf("java")): PassThroughModelLoadReport.File {
        load(file("model.yaml", text), languages = languages)
        return report().single()
    }

    @Test
    fun `valid java file reports the number of loaded models`() {
        val path = file("models.yaml", javaModels)
        val models = load(path)

        assertEquals(
            PassThroughModelLoadReport.File(path.toAbsolutePath().toString(), "java", models = 2),
            report().single(),
        )
        assertEquals(2, models.of(javaLoader).single().passThrough?.size)
    }

    @Test
    fun `syntax error is reported with its location`() {
        val error = assertNotNull(loadOne("language: java\npassThrough: [\n  - {function: \n").error)
        assertEquals(3, error.line)
        assertEquals(3, error.column)
    }

    @Test
    fun `unknown field is reported with its path`() {
        val file = loadOne("language: java\nfoo: 1\npassThrough: []\n")
        assertEquals("java", file.language)
        assertEquals(0, file.models)
        val error = assertNotNull(file.error)
        assertTrue(error.message.startsWith("Unknown property 'foo'"), error.message)
        assertEquals(2, error.line)
        assertEquals("foo", error.path)
    }

    @Test
    fun `missing required field is reported with its path`() {
        val error = assertNotNull(loadOne("language: java\npassThrough:\n- function: com.foo.Wrapper#wrap\n").error)
        assertEquals("Property 'copy' is required but it is missing.", error.message)
        assertEquals("passThrough[0]", error.path)
    }

    @Test
    fun `engine error for a bad position is reported`() {
        val file = loadOne(javaModels.replace("from: arg(0)", "from: foo"))
        assertEquals(PassThroughModelLoadReport.Error("Unexpected position: foo"), file.error)
        assertEquals(0, file.models)
    }

    @Test
    fun `file without language is reported`() {
        val file = loadOne("passThrough: []\n")
        assertNull(file.language)
        assertEquals(listOf("no language"), file.warnings)
    }

    @Test
    fun `file of an unsupported language is reported`() {
        val file = loadOne("language: python\npassThrough: []\n")
        assertEquals("python", file.language)
        assertEquals(listOf("language python is not supported"), file.warnings)
    }

    @Test
    fun `file of a language without a project is not loaded`() {
        val path = file("go.yaml", goModels)
        val models = load(path, languages = setOf("java"))

        assertEquals(PassThroughModelLoadReport.File(path.toAbsolutePath().toString(), "go", models = 0), report().single())
        assertEquals(emptyList(), models.of(goLoader))
    }

    @Test
    fun `root that is not a map is reported`() {
        val file = loadOne("- language: java\n")
        assertEquals(listOf("root is not a map"), file.warnings)
        assertNull(file.error)
    }

    @Test
    fun `missing path is reported`() {
        load(tmp.resolve("missing.yaml"))
        assertEquals(PassThroughModelLoadReport.Error("does not exist"), report().single().error)
    }

    @Test
    fun `java sections other than passThrough are reported`() {
        val file = loadOne("$javaModels\nsource: []\nsink: []\n")
        assertEquals(2, file.models)
        assertEquals(listOf("sections other than passThrough are ignored: source, sink"), file.warnings)
    }

    @Test
    fun `dropped go entries are reported`() {
        val path = file("go.yaml", goModels)
        val models = load(path, languages = setOf("go"))

        val file = report().single()
        assertEquals(1, file.models)
        assertEquals(
            listOf("passThrough[1] dropped: no function.package", "passThrough[2] dropped: no copy"),
            file.warnings,
        )
        assertEquals(2, models.of(goLoader).single().passThrough.size)
    }

    @Test
    fun `broken file is skipped and the good one is loaded`() {
        val broken = file("broken.yaml", javaModels.replace("from: arg(0)", "from: foo"))
        val good = file("good.yaml", javaModels)
        val models = load(broken, good)

        assertEquals(listOf(true, false), report().map { it.error != null })
        assertEquals(listOf(0, 2), report().map { it.models })
        assertEquals(2, models.of(javaLoader).single().passThrough?.size)
    }

    @Test
    fun `mixed run with a broken file writes one report with the models of every language`() {
        val options = object : CommonProjectAnalyzer.OptionProvider {
            override fun commonOptions() = CommonAnalysisOptions(
                customApproximationConfig = listOf(
                    file("broken.yaml", "language: java\npassThrough: 5\n"),
                    file("java.yaml", javaModels),
                    file("go.yaml", goModels),
                ),
                passthroughApproximationLoadReport = reportFile,
            )
            override fun javaOptions() = ProjectAnalysisOptions(common = commonOptions())
            override fun goOptions() = GoProjectAnalysisOptions(common = commonOptions())
        }
        val project = Project(
            javaProjects = listOf(JavaProject()),
            goProjects = listOf(GoProject(tmp.resolve("missing"))),
        )

        val status = CommonProjectAnalyzer(project, tmp.resolve("out"), runInTestMode = false, options).run()

        assertEquals(ProjectAnalysisStatus.OK, status)
        val files = report()
        assertEquals(listOf("java", "java", "go"), files.map { it.language })
        assertEquals(listOf(0, 2, 1), files.map { it.models })
        assertNotNull(files.first().error)
    }
}
