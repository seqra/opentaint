package org.opentaint.common.sast.rules

import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import mu.KLogging
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import java.nio.file.Path
import kotlin.io.path.extension
import kotlin.io.path.outputStream
import kotlin.io.path.readText
import kotlin.io.path.relativeTo
import kotlin.io.path.walk

private val logger = object : KLogging() {}.logger

fun CommonAnalysisOptions.loadSemgrepRules(strategy: LanguageStrategy<*, *>): SemgrepRuleLoader.RuleLoadResult {
    val trace = SemgrepLoadTrace()
    val rules = parseSemgrepRules(strategy, semgrepRuleSet, semgrepSeverity, semgrepRuleId, trace)
    semgrepRuleLoadTrace?.let { writeTrace(it, trace) }
    return rules
}

private fun writeTrace(traceFile: Path, trace: SemgrepLoadTrace) {
    val compressed = trace.compressed()
    runCatching {
        val pretty = Json { prettyPrint = true }
        traceFile.outputStream().bufferedWriter().use { it.write(pretty.encodeToString(compressed)) }
        logger.info { "Wrote semgrep load trace to $traceFile" }
    }.onFailure { logger.error(it) { "Failed to write semgrep load trace to $traceFile: ${it.message}" } }
}

private fun parseSemgrepRules(
    strategy: LanguageStrategy<*, *>,
    rulesPath: List<Path>,
    severity: List<Severity>,
    ruleId: List<String>,
    semgrepTrace: SemgrepLoadTrace,
): SemgrepRuleLoader.RuleLoadResult {
    val loader = SemgrepRuleLoader(listOf(strategy))
    val ruleExt = arrayOf("yaml", "yml")
    for (rulesRoot in rulesPath) {
        rulesRoot.walk().filter { it.extension in ruleExt }.forEach { rulePath ->
            val rel = rulePath.relativeTo(rulesRoot)
            loader.registerRuleSet(rulePath.readText(), rel, rulesRoot, semgrepTrace)
        }
    }
    val loaded = loader.loadRules(severity, ruleId)
    logger.info { "Total loaded ${loaded.rulesWithMeta.sumOf { it.first.size }} rules" }
    return loaded
}
