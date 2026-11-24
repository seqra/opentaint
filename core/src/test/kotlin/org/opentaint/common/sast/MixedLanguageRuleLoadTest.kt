package org.opentaint.common.sast

import kotlinx.serialization.json.Json
import kotlinx.serialization.json.jsonArray
import kotlinx.serialization.json.jsonObject
import kotlinx.serialization.json.jsonPrimitive
import org.opentaint.common.sast.rules.loadSemgrepRules
import org.opentaint.go.sast.project.GoProjectAnalysisOptions
import org.opentaint.jvm.sast.project.ProjectAnalysisOptions
import org.opentaint.project.GoProject
import org.opentaint.project.JavaProject
import org.opentaint.project.Project
import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import java.nio.file.Files
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.readText
import kotlin.io.path.writeText
import kotlin.test.Test
import kotlin.test.assertEquals

class MixedLanguageRuleLoadTest {
    private val tmp: Path = Files.createTempDirectory("mixed-language-rule-load-test")
    private val rulesRoot = tmp.resolve("rules").also { root ->
        root.resolve("java").createDirectories().resolve("rules.yaml").writeText(rule("java-rule", "java"))
        root.resolve("go").createDirectories().resolve("rules.yaml").writeText(rule("go-rule", "go"))
    }

    private fun rule(id: String, language: String) = """
        rules:
          - id: $id
            severity: ERROR
            message: m
            languages: [$language]
            mode: taint
            pattern-sources:
              - pattern: source(...)
            pattern-sinks:
              - pattern: sink(...)
    """.trimIndent()

    @Test
    fun `each language gets only its own rules`() {
        val rules = CommonAnalysisOptions(semgrepRuleSet = listOf(rulesRoot))
            .loadSemgrepRules(listOf(JavaLanguageStrategy(), GoLanguageStrategy()))

        assertEquals(setOf("java/rules.yaml:java-rule", "go/rules.yaml:go-rule"), rules.ruleIds())
        assertEquals(setOf("java/rules.yaml:java-rule"), rules.forLanguage("java").ruleIds())
        assertEquals(setOf("go/rules.yaml:go-rule"), rules.forLanguage("go").ruleIds())
    }

    @Test
    fun `mixed run writes one trace with the rules of every language`() {
        val traceFile = tmp.resolve("trace.json")
        val options = object : CommonProjectAnalyzer.OptionProvider {
            override fun commonOptions() = CommonAnalysisOptions(
                semgrepRuleSet = listOf(rulesRoot),
                semgrepRuleLoadTrace = traceFile,
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
        val tracedRuleIds = Json.parseToJsonElement(traceFile.readText()).jsonObject
            .getValue("fileTraces").jsonArray
            .flatMap { it.jsonObject.getValue("ruleTraces").jsonArray }
            .map { it.jsonObject.getValue("ruleId").jsonPrimitive.content }
        assertEquals(setOf("java/rules.yaml:java-rule", "go/rules.yaml:go-rule"), tracedRuleIds.toSet())
    }

    private fun SemgrepRuleLoader.RuleLoadResult.ruleIds() =
        rulesWithMeta.map { it.second.ruleId }.toSet()
}
