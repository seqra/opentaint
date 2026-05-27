package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.NormalizedSemgrepRule
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace

/** Rewrites a normalized rule's AST before action-list conversion (language-specific AST transforms). */
interface RuleRewriter<P : Any> {
    fun rewrite(
        rule: RuleWithMetaVars<NormalizedSemgrepRule<P>, ResolvedMetaVarInfo>
    ): List<RuleWithMetaVars<NormalizedSemgrepRule<P>, ResolvedMetaVarInfo>>
}

/** Everything language-specific in the pipeline, selected by [language]. */
interface LanguageStrategy<P : Any, R> {
    val language: String
    val parser: SemgrepPatternParser<P>
    val rewriter: RuleRewriter<P>
    val converter: ActionListBuilder<P>
    val typeOps: LanguageTypeOps
    val taintRuleStrategy: TaintRuleStrategy<R, *, *, *>

    /** Extract a concrete metavar constraint value from a parsed constraint pattern, or null. */
    fun extractMetaVarConstraint(pattern: P): MetaVarConstraint?

    enum class SinkDiscardMode {
        NONE, TRIVIAL_CONDITION, TRIVIAL_CONDITION_WITH_EMPTY_FUNCTION
    }

    fun parseMetaVar(
        metaVar: String,
        trace: SemgrepRuleLoadStepTrace,
    ): MetavarAtom?
}
