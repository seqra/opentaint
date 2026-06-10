package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonRule
import org.opentaint.semgrep.pattern.JoinRuleMetavarExpected
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.Metavar
import org.opentaint.semgrep.pattern.SemgrepPythonPattern
import org.opentaint.semgrep.pattern.SemgrepPythonPatternParser
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace

/**
 * Python semgrep rule support. The parser is implemented; the rewriter, converter,
 * type operations and taint-rule generation are TODO stubs.
 */
class PythonLanguageStrategy : LanguageStrategy<SemgrepPythonPattern, SerializedPythonRule> {
    override val language = "python"
    override val parser = SemgrepPythonPatternParser()
    override val rewriter = PythonRuleRewriter()
    override val converter = PythonPatternToActionListConverter()
    override val typeOps = PythonTypeOps
    override val taintRuleStrategy = PythonTaintStrategy

    /** TODO: extract concrete metavar constraints from Python patterns. */
    override fun extractMetaVarConstraint(pattern: SemgrepPythonPattern): MetaVarConstraint? = null

    override fun parseMetaVar(metaVar: String, trace: SemgrepRuleLoadStepTrace): MetavarAtom? {
        val parsed = parser.parseOrNull(metaVar, trace) ?: return null
        if (parsed !is Metavar) {
            trace.error(JoinRuleMetavarExpected(metaVar))
            return null
        }
        return MetavarAtom.create(parsed.name)
    }
}
