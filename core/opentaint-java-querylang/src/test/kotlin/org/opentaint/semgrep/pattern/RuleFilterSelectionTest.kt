package org.opentaint.semgrep.pattern

import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class RuleFilterSelectionTest {
    private val rules = """
        rules:
          - id: keep-me
            severity: ERROR
            message: x
            languages: [java]
            mode: taint
            pattern-sources:
              - pattern: source(...)
            pattern-sinks:
              - pattern: sink(...)
    """.trimIndent()

    private fun load(
        ruleIdFilter: List<String> = emptyList(),
        ruleIdExclude: List<String> = emptyList(),
        semgrepStyleRuleIdFilter: List<String> = emptyList(),
        semgrepStyleRuleIdExclude: List<String> = emptyList(),
    ): Pair<SemgrepRuleLoader.RuleLoadResult, SemgrepLoadTrace> {
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        val trace = SemgrepLoadTrace()
        loader.registerRuleSet(rules, Path("java/t.yaml"), Path("."), trace)
        val result = loader.loadRules(
            ruleIdFilter = ruleIdFilter,
            ruleIdExclude = ruleIdExclude,
            semgrepStyleRuleIdFilter = semgrepStyleRuleIdFilter,
            semgrepStyleRuleIdExclude = semgrepStyleRuleIdExclude,
            trace = trace,
        )
        return result to trace
    }

    private fun SemgrepLoadTrace.runEntries(severity: SemgrepErrorEntry.Severity) =
        entries.filterIsInstance<SemgrepErrorEntry>().filter { it.severity == severity }.map { it.message }

    @Test
    fun `every filter value that matches no rule gets a warning`() {
        val (result, trace) = load(
            ruleIdFilter = listOf("java/t.yaml:keep-me", "java/t.yaml:no-include"),
            ruleIdExclude = listOf("java/t.yaml:no-exclude"),
            semgrepStyleRuleIdFilter = listOf("java.keep-me", "java.no-style-include"),
            semgrepStyleRuleIdExclude = listOf("java.no-style-exclude"),
        )

        assertEquals(listOf("keep-me"), result.rulesWithMeta.map { it.second.shortRuleId })
        assertFalse(result.noRuleSelected)
        assertEquals(
            listOf("java/t.yaml:no-include", "java/t.yaml:no-exclude", "java.no-style-include", "java.no-style-exclude")
                .map { "Rule ID '$it' given to a rule filter matches no rule" },
            trace.runEntries(SemgrepErrorEntry.Severity.NON_BLOCKING),
        )
        assertTrue(trace.runEntries(SemgrepErrorEntry.Severity.BLOCKING).isEmpty())
    }

    @Test
    fun `filters that leave no rule report an error`() {
        listOf(
            load(semgrepStyleRuleIdFilter = listOf("java.no-such")),
            load(ruleIdExclude = listOf("java/t.yaml:keep-me")),
        ).forEach { (result, trace) ->
            assertTrue(result.rulesWithMeta.isEmpty())
            assertTrue(result.noRuleSelected)
            assertEquals(
                listOf("The rule filters leave no rule to run; the analysis is skipped"),
                trace.runEntries(SemgrepErrorEntry.Severity.BLOCKING),
            )
        }
    }

    @Test
    fun `no filter means nothing to check`() {
        val (result, trace) = load()
        assertFalse(result.noRuleSelected)
        assertTrue(trace.entries.isEmpty())
    }
}
