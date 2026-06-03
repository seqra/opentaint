package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.semgrep.pattern.JoinRuleMetavarExpected
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.SemgrepGoPattern
import org.opentaint.semgrep.pattern.SemgrepGoPatternParser
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace

class GoLanguageStrategy : LanguageStrategy<SemgrepGoPattern, GoSerializedItem> {
    override val language = "go"
    override val parser = SemgrepGoPatternParser()
    override val rewriter = GoRuleRewriter()
    override val converter = PatternToActionListConverter()
    override val typeOps = GoTypeOps
    override val taintRuleStrategy = GoTaintStrategy

    /** v1: Go metavar pattern-constraints are not extracted (treated as unconstrained). */
    override fun extractMetaVarConstraint(pattern: SemgrepGoPattern): MetaVarConstraint? = null

    override fun parseMetaVar(
        metaVar: String,
        trace: SemgrepRuleLoadStepTrace
    ): MetavarAtom? {
        val parsed = parser.parseOrNull(metaVar, trace) ?: return null
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

        fun globalReadAuxFnName(name: String) = "$GLOBAL_READ_AUX_FN_PREFIX$name"

        fun globalReadFieldOrNull(name: String): String? {
            if (!name.startsWith(GLOBAL_READ_AUX_FN_PREFIX)) return null
            return name.substring(GLOBAL_READ_AUX_FN_PREFIX.length)
        }

        fun fieldReadAuxFnName(field: String): String = "$FIELD_READ_AUX_FN_PREFIX$field"

        fun fieldReadFieldNull(name: String): String? {
            if (!name.startsWith(FIELD_READ_AUX_FN_PREFIX)) return null
            return name.substring(FIELD_READ_AUX_FN_PREFIX.length)
        }
    }
}
