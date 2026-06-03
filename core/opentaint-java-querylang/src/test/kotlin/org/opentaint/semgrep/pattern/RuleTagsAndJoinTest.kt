package org.opentaint.semgrep.pattern

import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class RuleTagsAndJoinTest {

    private fun parse(yml: String): SemgrepYamlRuleSet {
        val trace = SemgrepFileLoadTrace("test.yaml")
        return parseSemgrepYaml(yml, trace) ?: error("parse returned null; errors=${trace.errorMessages()}")
    }

    @Test
    fun `rule tags parse into a list`() {
        val rs = parse(
            """
            rules:
              - id: tagged
                severity: NOTE
                message: m
                languages: [java]
                tags:
                  - untrusted-data-source
                  - ssrf-source
                pattern: foo()
            """.trimIndent()
        )
        assertEquals(listOf("untrusted-data-source", "ssrf-source"), rs.rules.single().tags)
    }

    @Test
    fun `rule without tags defaults to empty`() {
        val rs = parse(
            """
            rules:
              - id: untagged
                severity: NOTE
                message: m
                languages: [java]
                pattern: foo()
            """.trimIndent()
        )
        assertTrue(rs.rules.single().tags.isEmpty())
    }

    @Test
    fun `join ref accepts either rule or tag`() {
        val rs = parse(
            """
            rules:
              - id: j
                severity: ERROR
                message: m
                languages: [java]
                mode: join
                join:
                  refs:
                    - tag: untrusted-data-source
                      as: untrusted-data
                    - rule: lib.yaml#sink
                      as: sink
                  on:
                    - 'untrusted-data.${'$'}X -> sink.${'$'}X'
            """.trimIndent()
        )
        val refs = rs.rules.single().join!!.refs
        assertEquals("untrusted-data-source", refs[0].tag)
        assertEquals(null, refs[0].rule)
        assertEquals("lib.yaml#sink", refs[1].rule)
        assertEquals(null, refs[1].tag)
    }

    private fun load(vararg files: Pair<String, String>): Pair<SemgrepRuleLoader.RuleLoadResult, SemgrepLoadTrace> {
        val trace = SemgrepLoadTrace()
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        for ((path, text) in files) {
            loader.registerRuleSet(text, Path(path), Path("."), trace)
        }
        return loader.loadRules() to trace
    }

    private fun loadedRuleIds(r: SemgrepRuleLoader.RuleLoadResult): List<String> =
        r.rulesWithMeta.map { it.second.shortRuleId }

    private val sinkLib = "lib/sink.yaml" to """
        rules:
          - id: ssrf-sink
            options: { lib: true }
            severity: NOTE
            message: sink
            languages: [java]
            patterns:
              - pattern: sink(${'$'}X)
    """.trimIndent()

    private val servletSource = "lib/servlet.yaml" to """
        rules:
          - id: servlet-source
            options: { lib: true }
            tags: [untrusted-data-source]
            severity: NOTE
            message: src
            languages: [java]
            patterns:
              - pattern: servletSource()
    """.trimIndent()

    @Test
    fun `tag ref expanding to no rules is a hard error`() {
        val (_, trace) = load(
            sinkLib,
            "ssrf.yaml" to """
                rules:
                  - id: ssrf
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - tag: untrusted-data-source
                          as: untrusted-data
                        - rule: lib/sink.yaml#ssrf-sink
                          as: sink
                      on:
                        - 'untrusted-data.${'$'}X -> sink.${'$'}X'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("no rule declares that tag") }, trace.errorMessages().toString())
    }

    @Test
    fun `ref with neither rule nor tag errors`() {
        val (_, trace) = load(
            sinkLib,
            "j.yaml" to """
                rules:
                  - id: j
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - as: x
                        - rule: lib/sink.yaml#ssrf-sink
                          as: sink
                      on:
                        - 'x.${'$'}X -> sink.${'$'}X'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("neither was given") }, trace.errorMessages().toString())
    }

    @Test
    fun `ref with both rule and tag errors`() {
        val (_, trace) = load(
            sinkLib, servletSource,
            "j.yaml" to """
                rules:
                  - id: j
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - rule: lib/servlet.yaml#servlet-source
                          tag: untrusted-data-source
                          as: x
                        - rule: lib/sink.yaml#ssrf-sink
                          as: sink
                      on:
                        - 'x.${'$'}X -> sink.${'$'}X'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("both were given") }, trace.errorMessages().toString())
    }

    @Test
    fun `two refs sharing one alias is rejected`() {
        val (_, trace) = load(
            sinkLib, servletSource,
            "j.yaml" to """
                rules:
                  - id: j
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - rule: lib/servlet.yaml#servlet-source
                          as: dup
                        - rule: lib/sink.yaml#ssrf-sink
                          as: dup
                      on:
                        - 'dup.${'$'}X -> dup.${'$'}X'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("declared by more than one ref") }, trace.errorMessages().toString())
    }

    @Test
    fun `ref to a join rule errors`() {
        val (_, trace) = load(
            sinkLib,
            "inner.yaml" to """
                rules:
                  - id: inner-join
                    options: { lib: true }
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - rule: lib/sink.yaml#ssrf-sink
                          as: s
                      on:
                        - 's.${'$'}X -> s.${'$'}X'
            """.trimIndent(),
            "j.yaml" to """
                rules:
                  - id: j
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - rule: lib/sink.yaml#ssrf-sink
                          as: src
                        - rule: inner.yaml#inner-join
                          as: sink
                      on:
                        - 'src.${'$'}X -> sink.${'$'}X'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("is a join rule") }, trace.errorMessages().toString())
    }

    @Test
    fun `conflicting alias metavars error`() {
        val (_, trace) = load(
            "lib/srcs.yaml" to """
                rules:
                  - id: a
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: a(${'$'}X) } ]
                  - id: b
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: b(${'$'}Y) } ]
            """.trimIndent(),
            sinkLib,
            "j.yaml" to """
                rules:
                  - id: j
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - rule: lib/srcs.yaml#a
                          as: a
                        - rule: lib/srcs.yaml#b
                          as: b
                        - rule: lib/sink.yaml#ssrf-sink
                          as: sink
                      on:
                        - 'a.${'$'}X -> sink.${'$'}T'
                        - 'b.${'$'}Y -> sink.${'$'}U'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("conflicting metavariables") }, trace.errorMessages().toString())
    }

    @Test
    fun `multi-sink join fans a tagged source union into several sinks`() {
        val (result, trace) = load(
            "lib/cmd.yaml" to """
                rules:
                  - id: src-a
                    options: { lib: true }
                    tags: [demo-src]
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: ${'$'}V = srcA() } ]
                  - id: src-b
                    options: { lib: true }
                    tags: [demo-src]
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: ${'$'}V = srcB() } ]
                  - id: sink-x
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: sinkX(${'$'}V) } ]
                  - id: sink-y
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: sinkY(${'$'}V) } ]
            """.trimIndent(),
            "j.yaml" to """
                rules:
                  - id: multi-sink
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - tag: demo-src
                          as: src
                        - rule: lib/cmd.yaml#sink-x
                          as: sinkx
                        - rule: lib/cmd.yaml#sink-y
                          as: sinky
                      on:
                        - 'src.${'$'}V -> sinkx.${'$'}V'
                        - 'src.${'$'}V -> sinky.${'$'}V'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().isEmpty(), trace.errorMessages().toString())
        assertTrue("multi-sink" in loadedRuleIds(result), "join rule should load; loaded=${loadedRuleIds(result)}")
    }

    @Test
    fun `chaining an alias as both source and sink is rejected`() {
        val (_, trace) = load(
            "lib/three.yaml" to """
                rules:
                  - id: a
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: a(${'$'}X) } ]
                  - id: b
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: b(${'$'}X) } ]
                  - id: c
                    options: { lib: true }
                    severity: NOTE
                    message: m
                    languages: [java]
                    patterns: [ { pattern: c(${'$'}X) } ]
            """.trimIndent(),
            "j.yaml" to """
                rules:
                  - id: j
                    severity: ERROR
                    message: m
                    languages: [java]
                    mode: join
                    join:
                      refs:
                        - rule: lib/three.yaml#a
                          as: a
                        - rule: lib/three.yaml#b
                          as: b
                        - rule: lib/three.yaml#c
                          as: c
                      on:
                        - 'a.${'$'}X -> b.${'$'}X'
                        - 'b.${'$'}X -> c.${'$'}X'
            """.trimIndent()
        )
        assertTrue(trace.errorMessages().any { it.contains("chains an alias") }, trace.errorMessages().toString())
    }
}

// Test-only helpers for reading the load trace.
fun SemgrepFileLoadTrace.errorMessages(): List<String> =
    entries.filterIsInstance<SemgrepErrorEntry>().map { it.message } +
        ruleTraces.flatMap { rt ->
            rt.entries.filterIsInstance<SemgrepErrorEntry>().map { it.message } +
                rt.steps.flatMap { st -> st.entries.filterIsInstance<SemgrepErrorEntry>().map { it.message } }
        }

fun SemgrepLoadTrace.errorMessages(): List<String> = fileTraces.flatMap { it.errorMessages() }
