package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.NormalizedSemgrepRule
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.SemgrepGoPattern

/** No AST rewrites for Go in v1. */
class GoRuleRewriter : RuleRewriter<SemgrepGoPattern> {
    override fun rewrite(rule: RuleWithMetaVars<NormalizedSemgrepRule<SemgrepGoPattern>, ResolvedMetaVarInfo>) = listOf(rule)
}
