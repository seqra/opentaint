package org.opentaint.semgrep.pattern.diff.load

import java.util.TreeMap

/**
 * Thread-confined in-memory implementation of [SemgrepRuleLoaderExtension].
 *
 * The loader invokes extensions synchronously. A collector is intended for one loader/load run and
 * does not perform synchronization. All exposed maps are immutable copies sorted by qualified id.
 */
class RuleDiffLoadCollector : SemgrepRuleLoaderExtension {
    private val collectedNormalRules = TreeMap<String, ParsedNormalRuleSnapshot>()
    private val collectedJoinRules = TreeMap<String, ParsedJoinRuleSnapshot>()
    private val collectedOverrides = TreeMap<String, ResolvedOverrideSnapshot>()
    private val collectedResolvedJoinRules = TreeMap<String, ResolvedJoinRuleSnapshot>()

    val normalRules: Map<String, ParsedNormalRuleSnapshot>
        get() = collectedNormalRules.toMap()

    val joinRules: Map<String, ParsedJoinRuleSnapshot>
        get() = collectedJoinRules.toMap()

    /** Overrides keyed by the qualified id of the rule that was overridden. */
    val overrides: Map<String, ResolvedOverrideSnapshot>
        get() = collectedOverrides.toMap()

    val resolvedJoinRules: Map<String, ResolvedJoinRuleSnapshot>
        get() = collectedResolvedJoinRules.toMap()

    override fun onNormalRuleParsed(rule: ParsedNormalRuleSnapshot) {
        collectedNormalRules[rule.descriptor.qualifiedRuleId] = rule
    }

    override fun onJoinRuleParsed(rule: ParsedJoinRuleSnapshot) {
        collectedJoinRules[rule.descriptor.qualifiedRuleId] = rule
    }

    override fun onOverrideResolved(override: ResolvedOverrideSnapshot) {
        collectedOverrides[override.targetRule.qualifiedRuleId] = override
    }

    override fun onJoinRuleResolved(rule: ResolvedJoinRuleSnapshot) {
        collectedResolvedJoinRules[rule.descriptor.qualifiedRuleId] = rule
    }
}
