package org.opentaint.common.sast.rules

import mu.KLogging
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import kotlin.io.path.extension
import kotlin.io.path.readText
import kotlin.io.path.relativeTo
import kotlin.io.path.walk

private val logger = object : KLogging() {}.logger

fun CommonAnalysisOptions.loadSemgrepRules(
    strategies: List<LanguageStrategy<*, *>>,
): SemgrepRuleLoader.RuleLoadResult {
    val trace = SemgrepLoadTrace()
    val rules = parseSemgrepRules(strategies, trace)
    semgrepRuleLoadTrace?.let { writeJson(it, SemgrepLoadTrace.serializer(), trace.compressed(), "semgrep load trace") }
    return rules
}

private fun CommonAnalysisOptions.parseSemgrepRules(
    strategies: List<LanguageStrategy<*, *>>,
    semgrepTrace: SemgrepLoadTrace,
): SemgrepRuleLoader.RuleLoadResult {
    val loader = SemgrepRuleLoader(strategies)
    val ruleExt = arrayOf("yaml", "yml")
    for (rulesRoot in semgrepRuleSet) {
        rulesRoot.walk().filter { it.extension in ruleExt }.forEach { rulePath ->
            val rel = rulePath.relativeTo(rulesRoot)
            loader.registerRuleSet(rulePath.readText(), rel, rulesRoot, semgrepTrace)
        }
    }
    val loaded = loader.loadRules(
        semgrepSeverity, semgrepRuleId, semgrepRuleIdExclude, semgrepStyleRuleId, semgrepStyleRuleIdExclude,
        useSemgrepStyleRuleId = sarifGenerationOptions.useSemgrepStyleId,
        trace = semgrepTrace,
    )
    logger.info { "Total loaded ${loaded.rulesWithMeta.sumOf { it.first.size }} rules" }
    return loaded
}
