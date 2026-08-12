package org.opentaint.semgrep.pattern.diff

import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.diff.automata.AutomataTraceDirection
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class RuleDiffServiceTest {
    private val service = RuleDiffService(listOf(JavaLanguageStrategy()))

    @Test
    fun `identical rules cancel all DNF cubes without automata comparison`() {
        val input = input(taintRule(source = "${'$'}X = source()"))

        val result = service.compare(input, input)

        assertEquals(RuleDiffStatus.EQUIVALENT, result.status)
        assertTrue(result.comparisonComplete)
        assertEquals(2, result.exactCubeMatches.size)
        assertTrue(result.automataCubeMatches.isEmpty())
        assertTrue(result.traceSamples.isEmpty())
    }

    @Test
    fun `changed unmatched cube is compiled and yields directional traces`() {
        val old = input(taintRule(source = "${'$'}X = oldSource()"))
        val new = input(taintRule(source = "${'$'}X = newSource()"))

        val result = service.compare(old, new)

        assertEquals(RuleDiffStatus.CHANGED, result.status)
        assertTrue(result.structureChanges.any { it.kind == StructureChangeKind.CUBE_EXPRESSION_CHANGED })
        assertTrue(result.automataCubeMatches.any { !it.equivalent })
        assertEquals(
            AutomataTraceDirection.entries.toSet(),
            result.traceSamples.map { it.direction }.toSet(),
        )
    }

    @Test
    fun `added sanitizer is structural change with a new-only sample`() {
        val old = input(taintRule(source = "${'$'}X = source()"))
        val new = input(
            """
            rules:
              - id: compared
                severity: NOTE
                message: test
                languages: [java]
                mode: taint
                pattern-sources:
                  - pattern: ${'$'}X = source()
                pattern-sinks:
                  - pattern: sink(${'$'}X)
                pattern-sanitizers:
                  - pattern: clean(${'$'}X)
            """.trimIndent()
        )

        val result = service.compare(old, new)

        assertEquals(RuleDiffStatus.CHANGED, result.status)
        assertEquals(1, result.addedCubes.size)
        assertTrue(result.traceSamples.any { it.direction == AutomataTraceDirection.NEW_ONLY })
    }

    @Test
    fun `different metavariable names are not alpha equivalent`() {
        val old = input(taintRule(source = "${'$'}X = source()"))
        val new = input(taintRule(source = "${'$'}Y = source()", sink = "sink(${'$'}Y)"))

        val result = service.compare(old, new)

        assertEquals(RuleDiffStatus.CHANGED, result.status)
        assertFalse(result.exactCubeMatches.any { (a, b) ->
            a.partKind == RulePartKind.SOURCE && b.partKind == RulePartKind.SOURCE
        })
    }

    @Test
    fun `both sides full load and an invalid selected side returns load failed`() {
        val valid = input(taintRule(source = "${'$'}X = source()"))
        val invalid = input(
            """
            rules:
              - id: compared
                severity: NOTE
                message: bad
                languages: [java]
                mode: taint
                pattern-sources:
                  - pattern: ${'$'}X = source()
            """.trimIndent()
        )

        val result = service.compare(valid, invalid)

        assertEquals(RuleDiffStatus.LOAD_FAILED, result.status)
        assertFalse(result.comparisonComplete)
        assertTrue(result.newLoadTrace.fileTraces.isNotEmpty())
    }

    @Test
    fun `join aliases and operations are compared before operand cubes`() {
        val libraries = listOf(
            RuleFileInput(
                Path("source.yaml"),
                """
                rules:
                  - id: source
                    options: { lib: true }
                    severity: NOTE
                    message: source
                    languages: [java]
                    pattern: ${'$'}X = source()
                """.trimIndent(),
            ),
            RuleFileInput(
                Path("sink.yaml"),
                """
                rules:
                  - id: sink
                    options: { lib: true }
                    severity: NOTE
                    message: sink
                    languages: [java]
                    pattern: sink(${'$'}X)
                """.trimIndent(),
            ),
        )
        fun join(alias: String) = RuleFileInput(
            Path("join.yaml"),
            """
            rules:
              - id: compared
                severity: NOTE
                message: join
                languages: [java]
                mode: join
                join:
                  refs:
                    - rule: source.yaml#source
                      as: $alias
                    - rule: sink.yaml#sink
                      as: sink
                  on:
                    - '$alias.${'$'}X -> sink.${'$'}X'
            """.trimIndent(),
        )

        val result = service.compare(
            RuleInput(libraries + join("source"), "compared"),
            RuleInput(libraries + join("origin"), "compared"),
        )

        assertEquals(RuleDiffStatus.CHANGED, result.status)
        assertTrue(result.structureChanges.any { it.kind == StructureChangeKind.JOIN_REF_REMOVED })
        assertTrue(result.structureChanges.any { it.kind == StructureChangeKind.JOIN_OPERATION_ADDED })
    }

    private fun input(yaml: String) = RuleInput(
        listOf(RuleFileInput(Path("rules.yaml"), yaml)),
        ruleId = "compared",
    )

    private fun taintRule(
        source: String,
        sink: String = "sink(${'$'}X)",
    ) = """
        rules:
          - id: compared
            severity: NOTE
            message: test
            languages: [java]
            mode: taint
            pattern-sources:
              - pattern: $source
            pattern-sinks:
              - pattern: $sink
    """.trimIndent()
}
