package org.opentaint.semgrep.pattern.diff.load

import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.RuleMetadata
import org.opentaint.semgrep.pattern.SemgrepJoinRuleOn
import org.opentaint.semgrep.pattern.SemgrepRule
import org.opentaint.semgrep.pattern.SemgrepYamlJoinRuleRef
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataJoinOperation
import java.nio.file.Path

/**
 * A read-only view of a rule accepted by [org.opentaint.semgrep.pattern.SemgrepRuleLoader].
 *
 * The qualified id includes the rule-set path, whereas [shortRuleId] is the id declared in YAML.
 */
data class ParsedRuleDescriptor(
    val qualifiedRuleId: String,
    val shortRuleId: String,
    val language: String?,
    val relativePath: Path,
    val isLibraryRule: Boolean,
    val isDisabled: Boolean,
)

data class ParsedNormalRuleSnapshot(
    val descriptor: ParsedRuleDescriptor,
    val rule: SemgrepRule<Formula>,
    val primitiveTracking: Boolean,
    val overrideTarget: String?,
    val metadata: RuleMetadata,
)

data class ParsedJoinRuleSnapshot(
    val descriptor: ParsedRuleDescriptor,
    val refs: List<SemgrepYamlJoinRuleRef>,
    val operations: List<SemgrepJoinRuleOn>,
    val metadata: RuleMetadata,
)

/** The loader replaced [targetRule] with [overridingRule]. */
data class ResolvedOverrideSnapshot(
    val targetRule: ParsedRuleDescriptor,
    val overridingRule: ParsedRuleDescriptor,
    val effectiveRuleId: String?,
)

data class ResolvedJoinItemSnapshot(
    val itemId: String,
    val alias: String,
    val referencedRuleId: String,
    val effectiveRuleId: String,
)

data class ResolvedJoinRuleSnapshot(
    val descriptor: ParsedRuleDescriptor,
    val items: Map<String, ResolvedJoinItemSnapshot>,
    val operations: List<TaintAutomataJoinOperation>,
)

/**
 * Additive observation points for consumers that need the loader's parsed and resolved structure.
 * Implementations must treat snapshots as immutable values and must not mutate their collections.
 */
interface SemgrepRuleLoaderExtension {
    fun onNormalRuleParsed(rule: ParsedNormalRuleSnapshot) = Unit
    fun onJoinRuleParsed(rule: ParsedJoinRuleSnapshot) = Unit
    fun onOverrideResolved(override: ResolvedOverrideSnapshot) = Unit
    fun onJoinRuleResolved(rule: ResolvedJoinRuleSnapshot) = Unit
}
