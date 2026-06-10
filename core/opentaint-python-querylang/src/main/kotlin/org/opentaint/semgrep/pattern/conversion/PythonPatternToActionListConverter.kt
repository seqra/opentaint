package org.opentaint.semgrep.pattern.conversion

import org.opentaint.semgrep.pattern.SemgrepPythonPattern
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace

/** TODO: convert a parsed Python pattern AST into a [SemgrepPatternActionList]. */
class PythonPatternToActionListConverter : ActionListBuilder<SemgrepPythonPattern> {
    override fun createActionList(
        pattern: SemgrepPythonPattern,
        semgrepTrace: SemgrepRuleLoadStepTrace,
    ): SemgrepPatternActionList? = TODO("Python pattern -> action list conversion not implemented")
}
