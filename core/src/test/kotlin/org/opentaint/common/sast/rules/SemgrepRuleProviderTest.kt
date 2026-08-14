package org.opentaint.common.sast.rules

import org.junit.jupiter.api.Test
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep.Structure
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep.TaintRuleGroup
import kotlin.test.assertEquals

class SemgrepRuleProviderTest {
    @Test
    fun `relevant rule ids retain only candidate graph with selected sink`() {
        val provider = TestProvider(
            listOf(
                taintRule("first", source = "source-a", sink = "sink-a"),
                taintRule("second", source = "source-b", sink = "sink-b"),
            )
        )

        val relevant = provider.relevantSemgrepRuleIds(
            setOf("source-a", "source-b", "sink-a")
        )

        assertEquals(setOf("source-a", "sink-a"), relevant)
    }

    @Test
    fun `relevant rule ids retain dependency chain`() {
        val sourceGroup = TaintRuleGroup(
            rules = listOf("source", "source-dependent"),
            ruleDependencies = mapOf("source-dependent" to setOf("source")),
            finalRuleIds = setOf("source-dependent"),
        )
        val sinkGroup = TaintRuleGroup(
            rules = listOf("sink"),
            finalRuleIds = setOf("sink"),
        )
        val provider = TestProvider(
            listOf(
                TaintRuleFromSemgrep(
                    ruleId = "dependent",
                    root = Structure.Taint(
                        sources = listOf(sourceGroup),
                        sinks = listOf(sinkGroup),
                        propagators = emptyList(),
                        sanitizers = emptyList(),
                    ),
                )
            )
        )

        val relevant = provider.relevantSemgrepRuleIds(
            setOf("source", "source-dependent", "sink")
        )

        assertEquals(setOf("source", "source-dependent", "sink"), relevant)
    }

    private class TestProvider(
        rules: List<TaintRuleFromSemgrep<String>>,
    ) : SemgrepRuleProvider<String, String>(rules) {
        override fun String.ruleItemId(): String = this
        override fun String.resolvedRuleId(): String = this
    }

    private fun taintRule(
        id: String,
        source: String,
        sink: String,
    ) = TaintRuleFromSemgrep(
        ruleId = id,
        root = Structure.Taint(
            sources = listOf(TaintRuleGroup(listOf(source), finalRuleIds = setOf(source))),
            sinks = listOf(TaintRuleGroup(listOf(sink), finalRuleIds = setOf(sink))),
            propagators = emptyList(),
            sanitizers = emptyList(),
        ),
    )
}
