package org.opentaint.common.sast.rules

import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

abstract class SemgrepRuleProvider<RuleItem, ResolvedRule>(
    val rules: List<TaintRuleFromSemgrep<RuleItem>>
) {
    private var ruleIdFilter: Set<String>? = null

    fun selectRelevantSemgrepRules(ruleIds: Set<String>) {
        // todo
    }

    abstract fun RuleItem.ruleItemId(): String?
    abstract fun ResolvedRule.resolvedRuleId(): String?

    fun <T : ResolvedRule> Iterable<T>.select(): Iterable<T> {
        val selectedRuleIds = ruleIdFilter ?: return this
        return filter { rule ->
            val rId = rule.resolvedRuleId() ?: return@filter true
            selectedRuleIds.contains(rId)
        }
    }
}
