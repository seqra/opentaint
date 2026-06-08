package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParsingResult
import org.opentaint.semgrep.go.pattern.conversion.GoPatternToActionListConverter
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.SemgrepTraceEntry.Step
import kotlin.test.Test
import kotlin.test.assertTrue

class CorpusConversionTest {
    private val parser = SemgrepGoPatternParser()
    private val converter = GoPatternToActionListConverter()
    private val noopTrace = SemgrepRuleLoadStepTrace(Step.BUILD_PARSE_SEMGREP_RULE)

    private fun loadPatterns(): List<String> {
        val text = javaClass.classLoader.getResource("patterns/corpus.txt")
            ?.readText() ?: error("corpus.txt not found on classpath")
        val regex = Regex("===PATTERN===\\s*\\n(.*?)\\n===END===", RegexOption.DOT_MATCHES_ALL)
        return regex.findAll(text).map { it.groupValues[1] }.toList()
    }

    @Test fun corpusConversionRate() {
        val patterns = loadPatterns()
        var parsed = 0
        var converted = 0
        for (p in patterns) {
            val r = parser.parseSemgrepGoPattern(p)
            if (r !is SemgrepGoPatternParsingResult.Ok) continue
            parsed++
            if (converter.createActionList(r.pattern, noopTrace) != null) converted++
        }
        println("Conversion: total=${patterns.size} parsed=$parsed converted=$converted")
        println("Failure reasons (top 30):")
        converter.failedTransformations.entries.sortedByDescending { it.value }.take(30)
            .forEach { (reason, count) -> println("  $count  $reason") }
        assertTrue(converted >= 210, "conversion rate regressed: converted=$converted (baseline 211)")
    }
}
