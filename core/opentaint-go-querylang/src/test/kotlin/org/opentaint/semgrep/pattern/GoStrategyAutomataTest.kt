package org.opentaint.semgrep.pattern

import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.SemgrepRuleAutomataBuilder
import org.opentaint.semgrep.pattern.conversion.automata.SemgrepRuleAutomata
import kotlin.test.Test
import kotlin.test.assertFalse

class GoStrategyAutomataTest {
    private fun buildAutomataRule(pattern: String): SemgrepRule<RuleWithMetaVars<SemgrepRuleAutomata, ResolvedMetaVarInfo>> {
        val builder = SemgrepRuleAutomataBuilder(GoLanguageStrategy())
        val rule: SemgrepRule<Formula> = SemgrepMatchingRule(listOf(Formula.LeafPattern(pattern)))
        val trace = SemgrepRuleLoadTrace("test-rule", "test-rule")
        return builder.build(rule, trace)
    }

    @Test
    fun packageCallBuildsAcceptingAutomaton() {
        val result = buildAutomataRule("fmt.Println(\$X)")
        assertFalse(result.isEmpty, "Go pattern 'fmt.Println(\$X)' produced no accepting automaton")
    }

    @Test
    fun methodCallOnMetavarReceiverBuildsAcceptingAutomaton() {
        val result = buildAutomataRule("\$DB.Query(\$Q)")
        assertFalse(result.isEmpty, "Go pattern '\$DB.Query(\$Q)' produced no accepting automaton")
    }
}
