package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.semgrep.pattern.ConcreteName
import org.opentaint.semgrep.pattern.JoinRuleMetavarExpected
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.NormalizedSemgrepRule
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.SemgrepJavaPattern
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.StringLiteral

class JavaRuleRewriter : RuleRewriter<SemgrepJavaPattern> {
    override fun rewrite(
        rule: RuleWithMetaVars<NormalizedSemgrepRule<SemgrepJavaPattern>, ResolvedMetaVarInfo>
    ): List<RuleWithMetaVars<NormalizedSemgrepRule<SemgrepJavaPattern>, ResolvedMetaVarInfo>> {
        var resultRules = listOf(rule.rule)

        resultRules = resultRules.flatMap(::rewriteCatchStatement)
        resultRules = resultRules.flatMap(::rewriteAddExpr)
        resultRules = resultRules.flatMap(::rewriteAssignEllipsis)
        resultRules = resultRules.flatMap(::rewriteMethodInvocationObj)
        resultRules = resultRules.flatMap(::rewriteStaticFieldAccess)
        resultRules = resultRules.flatMap(::rewriteEllipsisMethodInvocations)

        return resultRules.flatMap { resultRule ->
            val result = rewriteTypeNameWithMetaVar(resultRule, rule.metaVarInfo)
            result.first.map { RuleWithMetaVars(it, result.second) }
        }
    }
}

class JavaLanguageStrategy : LanguageStrategy<SemgrepJavaPattern, SerializedItem> {
    override val language = "java"
    override val parser = SemgrepPatternParser.createJava().cached()
    override val rewriter = JavaRuleRewriter()
    override val converter = ActionListBuilder.createJava().cached()
    override val typeOps = JavaTypeOps
    override val taintRuleStrategy = JavaTaintRuleStrategy

    override fun extractMetaVarConstraint(pattern: SemgrepJavaPattern): MetaVarConstraint? {
        if (pattern is StringLiteral && pattern.content is ConcreteName) {
            return MetaVarConstraint.Concrete(pattern.content.name)
        }
        val parts = tryExtractPatternDotSeparatedParts(pattern) ?: return null
        val names = tryExtractConcreteNames(parts) ?: return null
        return MetaVarConstraint.Concrete(names.joinToString(separator = "."))
    }

    override fun parseMetaVar(metaVar: String, trace: SemgrepRuleLoadStepTrace): MetavarAtom? {
        val parsed = parser.parseOrNull(metaVar, trace) ?: return null
        if (parsed !is Metavar) {
            trace.error(JoinRuleMetavarExpected(metaVar))
            return null
        }
        return MetavarAtom.create(parsed.name)
    }
}
