package org.opentaint.semgrep.go.pattern.conversion

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.semgrep.go.pattern.ExprStmt
import org.opentaint.semgrep.go.pattern.Metavar
import org.opentaint.semgrep.go.pattern.SemgrepGoPattern
import org.opentaint.semgrep.go.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.go.pattern.TopList
import org.opentaint.semgrep.pattern.JoinRuleMetavarExpected
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import org.opentaint.semgrep.pattern.conversion.MetavarAtom

class GoLanguageStrategy : LanguageStrategy<SemgrepGoPattern, GoSerializedItem> {
    override val language = "go"
    override val parser = SemgrepGoPatternParser()
    override val rewriter = GoRuleRewriter()
    override val converter = GoPatternToActionListConverter()
    override val typeOps = GoTypeOps
    override val taintRuleStrategy = GoTaintStrategy

    /** v1: Go metavar pattern-constraints are not extracted (treated as unconstrained). */
    override fun extractMetaVarConstraint(pattern: SemgrepGoPattern): MetaVarConstraint? = null

    override fun parseMetaVar(
        metaVar: String,
        trace: SemgrepRuleLoadStepTrace
    ): MetavarAtom? {
        val parsedPattern = parser.parseOrNull(metaVar, trace) ?: return null
        val parsed = parsedPattern.let { it as? TopList }?.items?.firstOrNull()?.let { it as? ExprStmt }?.expr
        if (parsed !is Metavar) {
            trace.error(JoinRuleMetavarExpected(metaVar))
            return null
        }
        return MetavarAtom.create(parsed.name)
    }

    companion object {
        const val GLOBAL_READ_AUX_FN_PREFIX = "$$<global>$$"
        const val FIELD_READ_AUX_FN_PREFIX = "$$<fieldread>$$"
        const val FIELD_READ_AUX_CLASS = "$$<fieldread-recv>$$"
        const val FIELD_AUX_MODIFIER = "$$<field-modifier>$$"
        const val FIELD_NAME_SEPARATOR = "$$<dot>$$"
        const val INDEX_AUX_FIELD_NAME = "$$[*]$$"

        fun globalReadAuxFnName(name: String) = "$GLOBAL_READ_AUX_FN_PREFIX$name"

        fun globalReadFieldOrNull(name: String): String? {
            if (!name.startsWith(GLOBAL_READ_AUX_FN_PREFIX)) return null
            return name.substring(GLOBAL_READ_AUX_FN_PREFIX.length)
        }

        fun fieldReadAuxFnName(field: String): String = "$FIELD_READ_AUX_FN_PREFIX$field"

        fun fieldReadFieldOrNull(name: String): String? {
            if (!name.startsWith(FIELD_READ_AUX_FN_PREFIX)) return null
            return name.substring(FIELD_READ_AUX_FN_PREFIX.length)
        }

        fun joinFieldNames(prev: String, next: String) = "$prev$FIELD_NAME_SEPARATOR$next"

        fun splitFieldNames(joinedName: String): List<String> = joinedName.split(FIELD_NAME_SEPARATOR)
    }
}
