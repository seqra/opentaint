package org.opentaint.semgrep.go.pattern.conversion

import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.conversion.GoImportRewriter.rewriteImports
import org.opentaint.semgrep.pattern.NormalizedSemgrepRule
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.conversion.RuleRewriter

class GoRuleRewriter : RuleRewriter<SemgrepGoPattern> {
    override fun rewrite(rule: RuleWithMetaVars<NormalizedSemgrepRule<SemgrepGoPattern>, ResolvedMetaVarInfo>): List<RuleWithMetaVars<NormalizedSemgrepRule<SemgrepGoPattern>, ResolvedMetaVarInfo>> {
        var resultRules = listOf(rule.rule)
        resultRules = resultRules.flatMap(::rewriteImports)
        return resultRules.map {
            RuleWithMetaVars(it, rule.metaVarInfo)
        }
    }
}
