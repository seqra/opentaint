package org.opentaint.semgrep.diff

import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.diff.RuleDiffResult
import org.opentaint.semgrep.pattern.diff.RuleDiffService
import org.opentaint.semgrep.pattern.diff.RuleDiffStatus
import java.nio.file.Files
import kotlin.io.path.Path
import kotlin.io.path.writeText
import kotlin.system.exitProcess

/** Small standalone frontend for the query-language rule-diff service. */
object RuleDiffRunner {
    @JvmStatic
    fun main(args: Array<String>) {
        val options = runCatching { parseArgs(args) }.getOrElse { error ->
            System.err.println(error.message)
            System.err.println(usage)
            exitProcess(1)
        }
        val strategies = when (options.language) {
            "java" -> listOf(JavaLanguageStrategy())
            "go" -> listOf(GoLanguageStrategy())
            null -> listOf(JavaLanguageStrategy(), GoLanguageStrategy())
            else -> error("Unsupported language: ${options.language}")
        }
        val result = RuleDiffService(strategies).comparePaths(
            options.oldPath,
            options.newPath,
            options.oldRuleId,
            options.newRuleId ?: options.oldRuleId,
        )
        val rendered = when (options.format) {
            "text" -> renderText(result, options.includeTraces)
            "json" -> renderJson(result, options.includeTraces)
            else -> error("Unsupported format: ${options.format}")
        }
        if (options.output == null) {
            println(rendered)
        } else {
            options.output.parent?.let(Files::createDirectories)
            options.output.writeText(rendered + "\n")
        }
        exitProcess(
            when (result.status) {
                RuleDiffStatus.EQUIVALENT -> 0
                RuleDiffStatus.CHANGED -> 2
                RuleDiffStatus.INCONCLUSIVE, RuleDiffStatus.LOAD_FAILED -> 1
            }
        )
    }

    private data class CliOptions(
        val oldPath: java.nio.file.Path,
        val newPath: java.nio.file.Path,
        val oldRuleId: String,
        val newRuleId: String?,
        val language: String?,
        val format: String,
        val output: java.nio.file.Path?,
        val includeTraces: Boolean,
    )

    private fun parseArgs(args: Array<String>): CliOptions {
        val positional = mutableListOf<String>()
        var oldRuleId: String? = null
        var newRuleId: String? = null
        var language: String? = null
        var format = "text"
        var output: java.nio.file.Path? = null
        var includeTraces = true
        var index = 0
        fun value(name: String): String {
            index++
            require(index < args.size) { "Missing value for $name" }
            return args[index]
        }
        while (index < args.size) {
            when (val arg = args[index]) {
                "--old-rule-id" -> oldRuleId = value(arg)
                "--new-rule-id" -> newRuleId = value(arg)
                "--language" -> language = value(arg).lowercase()
                "--format" -> format = value(arg).lowercase()
                "--output" -> output = Path(value(arg))
                "--no-traces" -> includeTraces = false
                "--help", "-h" -> throw IllegalArgumentException(usage)
                else -> if (arg.startsWith('-')) {
                    throw IllegalArgumentException("Unknown option: $arg")
                } else {
                    positional += arg
                }
            }
            index++
        }
        require(positional.size == 2) { "Expected OLD and NEW rule file or directory" }
        require(oldRuleId != null) { "--old-rule-id is required" }
        require(language == null || language in setOf("java", "go")) { "--language must be java or go" }
        require(format in setOf("text", "json")) { "--format must be text or json" }
        return CliOptions(
            Path(positional[0]), Path(positional[1]), oldRuleId, newRuleId,
            language, format, output, includeTraces,
        )
    }

    private fun renderText(result: RuleDiffResult, includeTraces: Boolean): String = buildString {
        appendLine("status: ${result.status}")
        appendLine("comparison-complete: ${result.comparisonComplete}")
        appendLine("old-rule: ${result.oldRule?.qualifiedRuleId ?: "<unavailable>"}")
        appendLine("new-rule: ${result.newRule?.qualifiedRuleId ?: "<unavailable>"}")
        result.loadFailure?.let { appendLine("load-failure: $it") }
        result.structureChanges.forEach { appendLine("structure: ${it.kind}: ${it.detail}") }
        result.removedCubes.forEach { appendLine("removed-cube: ${it.partKind} ${it.patterns}") }
        result.addedCubes.forEach { appendLine("added-cube: ${it.partKind} ${it.patterns}") }
        result.inconclusiveComparisons.forEach { appendLine("inconclusive: ${it.reason}") }
        if (includeTraces) result.traceSamples.forEach { witness ->
            appendLine("trace: ${witness.direction} ${witness.observation}: ${witness.detail}")
            witness.steps.forEach { appendLine("  ${it.eventKind}: ${it.label}") }
        }
    }.trimEnd()

    private fun renderJson(result: RuleDiffResult, includeTraces: Boolean): String = buildString {
        fun field(name: String, value: String, comma: Boolean = true) {
            append("  \"").append(name.json()).append("\": \"").append(value.json()).append('"')
            if (comma) append(',')
            appendLine()
        }
        appendLine("{")
        field("status", result.status.name)
        appendLine("  \"comparisonComplete\": ${result.comparisonComplete},")
        appendLine("  \"hasProvenChanges\": ${result.hasProvenChanges},")
        field("oldRule", result.oldRule?.qualifiedRuleId.orEmpty())
        field("newRule", result.newRule?.qualifiedRuleId.orEmpty())
        field("loadFailure", result.loadFailure.orEmpty())
        appendLine("  \"structureChanges\": [")
        result.structureChanges.forEachIndexed { index, change ->
            append("    {\"kind\": \"").append(change.kind.name.json())
                .append("\", \"detail\": \"").append(change.detail.json()).append("\"}")
            if (index != result.structureChanges.lastIndex) append(',')
            appendLine()
        }
        appendLine("  ],")
        appendLine("  \"addedCubes\": ${cubeJson(result.addedCubes)},")
        appendLine("  \"removedCubes\": ${cubeJson(result.removedCubes)},")
        appendLine("  \"inconclusive\": [${result.inconclusiveComparisons.joinToString { "\"${it.reason.json()}\"" }}],")
        val traces = if (includeTraces) result.traceSamples else emptyList()
        appendLine("  \"traces\": [")
        traces.forEachIndexed { index, witness ->
            append("    {\"direction\": \"").append(witness.direction.name)
                .append("\", \"observation\": \"").append(witness.observation.name)
                .append("\", \"detail\": \"").append(witness.detail.json()).append("\"}")
            if (index != traces.lastIndex) append(',')
            appendLine()
        }
        appendLine("  ]")
        append('}')
    }

    private fun cubeJson(cubes: List<org.opentaint.semgrep.pattern.diff.CubeReference>): String =
        cubes.joinToString(prefix = "[", postfix = "]") { cube ->
            "{\"partKind\":\"${cube.partKind}\",\"patterns\":[${cube.patterns.joinToString { "\"${it.json()}\"" }}]}"
        }

    private fun String.json(): String = buildString {
        for (char in this@json) when (char) {
            '\\' -> append("\\\\")
            '"' -> append("\\\"")
            '\n' -> append("\\n")
            '\r' -> append("\\r")
            '\t' -> append("\\t")
            else -> append(char)
        }
    }

    private val usage = """
        Usage: RuleDiffRunner OLD NEW --old-rule-id ID [options]
          --new-rule-id ID
          --language java|go
          --format text|json
          --output PATH
          --no-traces
    """.trimIndent()
}
