package org.opentaint.common.sast

import kotlinx.serialization.json.Json
import kotlinx.serialization.json.jsonArray
import kotlinx.serialization.json.jsonObject
import org.opentaint.common.sast.sarif.SarifGenerationOptions
import org.opentaint.go.sast.project.GoProjectAnalysisOptions
import org.opentaint.jvm.sast.project.ProjectAnalysisOptions
import org.opentaint.project.GoProject
import org.opentaint.project.Project
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.readText
import kotlin.io.path.writeText
import kotlin.test.Test
import kotlin.test.assertEquals

class EmptyRuleSelectionTest {
    private val tmp: Path = Files.createTempDirectory("empty-rule-selection-test")

    @Test
    fun `selection without rules skips the analysis and writes an empty report`() {
        val rulesRoot = tmp.resolve("rules").createDirectories()
        rulesRoot.resolve("rules.yaml").writeText(
            """
            rules:
              - id: go-rule
                severity: ERROR
                message: m
                languages: [go]
                mode: taint
                pattern-sources:
                  - pattern: source(...)
                pattern-sinks:
                  - pattern: sink(...)
            """.trimIndent()
        )
        val options = object : CommonProjectAnalyzer.OptionProvider {
            override fun commonOptions() = CommonAnalysisOptions(
                semgrepRuleSet = listOf(rulesRoot),
                semgrepStyleRuleId = listOf("no-such-rule"),
            )
            override fun javaOptions() = ProjectAnalysisOptions(common = commonOptions())
            override fun goOptions() = GoProjectAnalysisOptions(common = commonOptions())
        }
        val toolchain = tmp.resolve("goroot").createDirectories()
        val project = Project(goProjects = listOf(GoProject(tmp.resolve("go_0"), toolchain)))
        val outputDir = tmp.resolve("out").createDirectories()

        val status = CommonProjectAnalyzer(project, outputDir, runInTestMode = false, options).run()

        assertEquals(ProjectAnalysisStatus.OK, status)
        val runs = Json.parseToJsonElement(outputDir.resolve(SarifGenerationOptions.DEFAULT_FILE_NAME).readText())
            .jsonObject.getValue("runs").jsonArray
        assertEquals(1, runs.size)
        assertEquals(0, runs.single().jsonObject.getValue("results").jsonArray.size)
    }
}
