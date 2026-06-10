package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.NormalizedSemgrepRule
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.SemgrepPythonPattern

/** No AST rewrites for Python yet. */
class PythonRuleRewriter : RuleRewriter<SemgrepPythonPattern> {
    override fun rewrite(
        rule: RuleWithMetaVars<NormalizedSemgrepRule<SemgrepPythonPattern>, ResolvedMetaVarInfo>
    ) = listOf(rule)
}
