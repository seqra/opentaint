package org.opentaint.semgrep.pattern

import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

class RuleIdExcludeTest {
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
          - id: drop-me
            severity: ERROR
            message: x
            languages: [java]
            mode: taint
            pattern-sources:
              - pattern: source(...)
            pattern-sinks:
              - pattern: sink(...)
    """.trimIndent()

    private fun loadedRuleIds(
        ruleIdFilter: List<String> = emptyList(),
        ruleIdExclude: List<String> = emptyList(),
    ): Set<String> {
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        loader.registerRuleSet(rules, Path("t.yaml"), Path("."), SemgrepLoadTrace())
        return loader.loadRules(ruleIdFilter = ruleIdFilter, ruleIdExclude = ruleIdExclude)
            .rulesWithMeta.map { it.second.shortRuleId }.toSet()
    }

    @Test
    fun `no filters loads every rule`() {
        assertEquals(setOf("keep-me", "drop-me"), loadedRuleIds())
    }

    @Test
    fun `exclusion drops only the matching rule`() {
        assertEquals(setOf("keep-me"), loadedRuleIds(ruleIdExclude = listOf("t.yaml:drop-me")))
    }

    @Test
    fun `exclusion composes with the inclusion filter`() {
        assertEquals(
            emptySet(),
            loadedRuleIds(
                ruleIdFilter = listOf("t.yaml:drop-me"),
                ruleIdExclude = listOf("t.yaml:drop-me"),
            ),
        )
    }

    @Test
    fun `excluding an unknown id changes nothing`() {
        assertEquals(setOf("keep-me", "drop-me"), loadedRuleIds(ruleIdExclude = listOf("t.yaml:no-such")))
    }

    @Test
    fun `excluding an explicitly referenced lib rule prevents the join from loading`() {
        val lib = """
            rules:
              - id: taint-source
                options:
                  lib: true
                severity: NOTE
                message: m
                languages: [java]
                patterns:
                  - pattern: source(${'$'}UNTRUSTED);
        """.trimIndent()
        val join = """
            rules:
              - id: joined
                severity: ERROR
                message: m
                languages: [java]
                mode: join
                join:
                  refs:
                    - rule: lib.yaml#taint-source
                      as: src
                    - rule: inline-sink
                      as: sink
                  on:
                    - 'src.${'$'}UNTRUSTED -> sink.${'$'}UNTRUSTED'
              - id: inline-sink
                options:
                  lib: true
                severity: NOTE
                message: m
                languages: [java]
                patterns:
                  - pattern: sink(${'$'}UNTRUSTED);
        """.trimIndent()

        fun load(exclude: List<String>): Pair<List<String>, SemgrepLoadTrace> {
            val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
            val trace = SemgrepLoadTrace()
            loader.registerRuleSet(lib, Path("lib.yaml"), Path("."), trace)
            loader.registerRuleSet(join, Path("j.yaml"), Path("."), trace)
            val ids = loader.loadRules(ruleIdExclude = exclude).rulesWithMeta.map { it.second.shortRuleId }
            return ids to trace
        }

        // Control: the join must load at all before the exclusion claim means anything.
        assertEquals(listOf("joined"), load(emptyList()).first)
        val (excluded, trace) = load(listOf("lib.yaml:taint-source"))
        assertTrue(excluded.isEmpty())
        assertTrue(trace.errorMessages().isEmpty(), trace.errorMessages().toString())
    }

    @Test
    fun `excluding a tagged lib rule removes it from the tag expansion`() {
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
              - id: joined
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
              - id: inline-sink
                options: { lib: true }
                severity: NOTE
                message: m
                languages: [java]
                patterns:
                  - pattern: sink(${'$'}UNTRUSTED);
        """.trimIndent()

        fun load(exclude: List<String>): Pair<SemgrepRuleLoader.RuleLoadResult, SemgrepLoadTrace> {
            val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
            val trace = SemgrepLoadTrace()
            loader.registerRuleSet(lib, Path("lib.yaml"), Path("."), trace)
            loader.registerRuleSet(join, Path("j.yaml"), Path("."), trace)
            return loader.loadRules(ruleIdExclude = exclude) to trace
        }

        val (result, trace) = load(listOf("lib.yaml:source-a"))
        assertTrue(trace.errorMessages().isEmpty(), trace.errorMessages().toString())
        val root = assertIs<TaintRuleFromSemgrep.Structure.Join<*>>(result.rulesWithMeta.single().first.root)
        assertEquals(
            setOf("lib.yaml:source-b"),
            root.branches.flatMap { it.leftOperands }.map { it.ruleId }.toSet(),
        )

        val (emptyResult, emptyTrace) = load(listOf("lib.yaml:source-a", "lib.yaml:source-b"))
        assertTrue(emptyResult.rulesWithMeta.isEmpty())
        assertTrue(emptyTrace.errorMessages().isEmpty(), emptyTrace.errorMessages().toString())
    }
}
