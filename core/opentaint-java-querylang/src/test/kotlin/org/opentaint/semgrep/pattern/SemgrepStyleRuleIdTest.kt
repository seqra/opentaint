package org.opentaint.semgrep.pattern

import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

class SemgrepStyleRuleIdTest {
    private fun taintRules(vararg ids: String) = ids.joinToString("\n", prefix = "rules:\n") { id ->
        """
          - id: $id
            severity: ERROR
            message: x
            languages: [java]
            mode: taint
            pattern-sources:
              - pattern: source(...)
            pattern-sinks:
              - pattern: sink(...)
        """.trimIndent().prependIndent("  ")
    }

    private val ruleSets = mapOf(
        "java/security/a.yaml" to taintRules("keep-me", "drop-me", "dup"),
        "java/security/b.yaml" to taintRules("dup"),
    )

    private fun load(
        ruleSets: Map<String, String> = this.ruleSets,
        ruleIdFilter: List<String> = emptyList(),
        ruleIdExclude: List<String> = emptyList(),
        semgrepStyleRuleIdFilter: List<String> = emptyList(),
        semgrepStyleRuleIdExclude: List<String> = emptyList(),
        useSemgrepStyleRuleId: Boolean = false,
    ): Pair<SemgrepRuleLoader.RuleLoadResult, SemgrepLoadTrace> {
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        val trace = SemgrepLoadTrace()
        ruleSets.forEach { (path, text) -> loader.registerRuleSet(text, Path(path), Path("."), trace) }
        val result = loader.loadRules(
            ruleIdFilter = ruleIdFilter,
            ruleIdExclude = ruleIdExclude,
            semgrepStyleRuleIdFilter = semgrepStyleRuleIdFilter,
            semgrepStyleRuleIdExclude = semgrepStyleRuleIdExclude,
            useSemgrepStyleRuleId = useSemgrepStyleRuleId,
        )
        return result to trace
    }

    private fun loadedRuleIds(
        ruleIdFilter: List<String> = emptyList(),
        semgrepStyleRuleIdFilter: List<String> = emptyList(),
        semgrepStyleRuleIdExclude: List<String> = emptyList(),
    ): Set<String> = load(
        ruleIdFilter = ruleIdFilter,
        semgrepStyleRuleIdFilter = semgrepStyleRuleIdFilter,
        semgrepStyleRuleIdExclude = semgrepStyleRuleIdExclude,
    ).first.rulesWithMeta.map { it.second.ruleId }.toSet()

    @Test
    fun `semgrep-style id selects the rule`() {
        assertEquals(setOf("java/security/a.yaml:keep-me"), loadedRuleIds(semgrepStyleRuleIdFilter = listOf("java.security.keep-me")))
    }

    @Test
    fun `semgrep-style id selects every rule that shares it`() {
        assertEquals(
            setOf("java/security/a.yaml:dup", "java/security/b.yaml:dup"),
            loadedRuleIds(semgrepStyleRuleIdFilter = listOf("java.security.dup")),
        )
    }

    @Test
    fun `semgrep-style id that matches no rule selects nothing`() {
        assertEquals(emptySet(), loadedRuleIds(semgrepStyleRuleIdFilter = listOf("java.security.no-such")))
    }

    @Test
    fun `semgrep-style and canonical ids select together`() {
        assertEquals(
            setOf("java/security/a.yaml:keep-me", "java/security/a.yaml:drop-me"),
            loadedRuleIds(
                ruleIdFilter = listOf("java/security/a.yaml:keep-me"),
                semgrepStyleRuleIdFilter = listOf("java.security.drop-me"),
            ),
        )
    }

    @Test
    fun `semgrep-style exclusion drops every rule that shares it`() {
        assertEquals(
            setOf("java/security/a.yaml:keep-me", "java/security/a.yaml:drop-me"),
            loadedRuleIds(semgrepStyleRuleIdExclude = listOf("java.security.dup")),
        )
    }

    @Test
    fun `semgrep-style exclusion applies after the inclusion filter`() {
        assertEquals(
            emptySet(),
            loadedRuleIds(
                semgrepStyleRuleIdFilter = listOf("java.security.drop-me"),
                semgrepStyleRuleIdExclude = listOf("java.security.drop-me"),
            ),
        )
    }

    @Test
    fun `semgrep-style exclusion of lib rules cascades into joins`() {
        val lib = """
            rules:
              - id: source-a
                options: { lib: true }
                tags: [taint-source]
                severity: NOTE
                message: m
                languages: [java]
                patterns:
                  - pattern: ${'$'}UNTRUSTED = sourceA();
              - id: source-b
                options: { lib: true }
                tags: [taint-source]
                severity: NOTE
                message: m
                languages: [java]
                patterns:
                  - pattern: ${'$'}UNTRUSTED = sourceB();
        """.trimIndent()
        val join = """
            rules:
              - id: joined-by-tag
                severity: ERROR
                message: m
                languages: [java]
                mode: join
                join:
                  refs:
                    - tag: taint-source
                      as: src
                    - rule: inline-sink
                      as: sink
                  on:
                    - 'src.${'$'}UNTRUSTED -> sink.${'$'}UNTRUSTED'
              - id: joined-by-rule
                severity: ERROR
                message: m
                languages: [java]
                mode: join
                join:
                  refs:
                    - rule: java/lib/sources.yaml#source-b
                      as: src
                    - rule: inline-sink
                      as: sink
                  on:
                    - 'src.${'$'}UNTRUSTED -> sink.${'$'}UNTRUSTED'
              - id: inline-sink
                options: { lib: true }
                severity: NOTE
                message: m
                languages: [java]
                patterns:
                  - pattern: sink(${'$'}UNTRUSTED);
        """.trimIndent()
        val joinRuleSets = mapOf("java/lib/sources.yaml" to lib, "java/security/j.yaml" to join)

        val (result, trace) = load(joinRuleSets, semgrepStyleRuleIdExclude = listOf("java.lib.source-a"))
        assertTrue(trace.errorMessages().isEmpty(), trace.errorMessages().toString())
        val byTag = result.rulesWithMeta.single { it.second.shortRuleId == "joined-by-tag" }.first.root
        assertEquals(
            setOf("java/lib/sources.yaml:source-b"),
            assertIs<TaintRuleFromSemgrep.Structure.Join<*>>(byTag).branches
                .flatMap { it.leftOperands }.map { it.ruleId }.toSet(),
        )

        val (excludedB, _) = load(joinRuleSets, semgrepStyleRuleIdExclude = listOf("java.lib.source-b"))
        assertEquals(listOf("joined-by-tag"), excludedB.rulesWithMeta.map { it.second.shortRuleId })

        val (excludedSink, _) = load(joinRuleSets, semgrepStyleRuleIdExclude = listOf("java.security.inline-sink"))
        assertTrue(excludedSink.rulesWithMeta.isEmpty())
    }

    private fun SemgrepLoadTrace.collisionWarnings(): Map<String, List<String>> =
        fileTraces.flatMap { file -> file.ruleTraces }.associate { rule ->
            rule.ruleId to rule.steps.flatMap { it.entries }.filterIsInstance<SemgrepErrorEntry>()
                .filter { "Semgrep-style rule ID" in it.message }
                .onEach { assertEquals(SemgrepErrorEntry.Severity.NON_BLOCKING, it.severity) }
                .map { it.message }
        }.filterValues { it.isNotEmpty() }

    @Test
    fun `colliding rules get a warning naming each other when semgrep-style ids are in use`() {
        val warnings = load(useSemgrepStyleRuleId = true).second.collisionWarnings()

        assertEquals(setOf("java/security/a.yaml:dup", "java/security/b.yaml:dup"), warnings.keys)
        assertTrue(warnings.getValue("java/security/a.yaml:dup").single().contains("'java/security/b.yaml:dup'"))
        assertTrue(warnings.getValue("java/security/b.yaml:dup").single().contains("'java/security/a.yaml:dup'"))
    }

    @Test
    fun `semgrep-style filters report collisions`() {
        val expected = setOf("java/security/a.yaml:dup", "java/security/b.yaml:dup")
        assertEquals(expected, load(semgrepStyleRuleIdFilter = listOf("java.security.keep-me")).second.collisionWarnings().keys)
        assertEquals(expected, load(semgrepStyleRuleIdExclude = listOf("java.security.keep-me")).second.collisionWarnings().keys)
    }

    @Test
    fun `collisions are not reported without semgrep-style ids`() {
        assertEquals(emptyMap(), load().second.collisionWarnings())
        assertEquals(emptyMap(), load(ruleIdFilter = listOf("java/security/a.yaml:dup")).second.collisionWarnings())
    }
}
