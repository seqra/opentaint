package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.SemgrepGoPattern
import org.opentaint.semgrep.pattern.SemgrepGoPatternParser

class GoLanguageStrategy : LanguageStrategy<SemgrepGoPattern> {
    override val language = "go"
    override val parser = SemgrepGoPatternParser()
    override val rewriter = GoRuleRewriter()
    override val converter = PatternToActionListConverter()
    override val typeOps = GoTypeOps

    /** v1: Go metavar pattern-constraints are not extracted (treated as unconstrained). */
    override fun extractMetaVarConstraint(pattern: SemgrepGoPattern): MetaVarConstraint? = null
}
