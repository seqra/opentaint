package org.opentaint.semgrep

import org.opentaint.semgrep.pattern.SemgrepErrorEntry
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertTrue

class MetavarPatternBothReproTest {
    private fun blockingErrors(ruleText: String): List<String> {
        val trace = SemgrepLoadTrace()
        val loader = SemgrepRuleLoader(listOf(JavaLanguageStrategy()))
        loader.registerRuleSet(ruleText, Path("repro.yaml"), Path("."), trace)
        loader.loadRules()
        return buildList {
            for (file in trace.fileTraces) {
                file.entries.filterIsInstance<SemgrepErrorEntry>().forEach { add("${it.severity}/${it.step}: ${it.message}") }
                for (rule in file.ruleTraces) {
                    rule.entries.filterIsInstance<SemgrepErrorEntry>().forEach { add("${it.severity}/${it.step}: ${it.message}") }
                    rule.steps.forEach { s -> s.entries.filterIsInstance<SemgrepErrorEntry>().forEach { add("${it.severity}/${it.step}: ${it.message}") } }
                }
            }
        }
    }

    @Test
    fun `metavariable-pattern on BOTH COND and METHOD`() {
        val rule = """
            rules:
              - id: repro-both-metavar-pattern
                options:
                  lib: true
                severity: NOTE
                message: x
                languages: [java]
                mode: taint
                pattern-sinks:
                  - patterns:
                      - pattern: |
                          (org.springframework.ldap.query.LdapQuery ${'$'}Q) = (org.springframework.ldap.query.ConditionCriteria ${'$'}C).${'$'}COND(${'$'}UNTRUSTED);
                          ...;
                          (${'$'}CTXTYPE ${'$'}CTX).${'$'}METHOD(${'$'}Q, ...);
                      - metavariable-pattern:
                          metavariable: ${'$'}COND
                          pattern-either:
                            - pattern: is
                            - pattern: like
                            - pattern: whitespaceWildcardsLike
                            - pattern: gte
                            - pattern: lte
                      - metavariable-pattern:
                          metavariable: ${'$'}CTXTYPE
                          pattern-either:
                            - pattern: org.springframework.ldap.core.LdapTemplate
                      - metavariable-pattern:
                          metavariable: ${'$'}METHOD
                          pattern-either:
                            - pattern: find
                            - pattern: findOne
                            - pattern: search
                            - pattern: searchForContext
                            - pattern: searchForObject
                            - pattern: list
                            - pattern: lookup
                            - pattern: authenticate
                            - pattern: findByDn
                            - pattern: listBindings
                            - pattern: lookupContext
                            - pattern: rename
                      - focus-metavariable: ${'$'}UNTRUSTED
        """.trimIndent()

        val errors = blockingErrors(rule)
        assertTrue(errors.isEmpty(), "metavariable-pattern on both COND and METHOD still errors:\n" + errors.joinToString("\n"))
    }
}
