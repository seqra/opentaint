package org.opentaint.semgrep.go.pattern.conversion.go

import org.opentaint.semgrep.go.pattern.conversion.GoConcreteType
import org.opentaint.semgrep.go.pattern.conversion.GoTaintRuleGenerationCtx
import org.opentaint.semgrep.pattern.MetaVarConstraint
import org.opentaint.semgrep.pattern.MetaVarConstraintFormula
import org.opentaint.semgrep.pattern.PlaceholderTypeName
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.conversion.TypeConstraint
import org.opentaint.semgrep.pattern.conversion.taint.MetaVarConstraintOrPlaceHolder
import org.opentaint.semgrep.pattern.transform

internal fun GoTaintRuleGenerationCtx.goTypeMatcher(
    typeName: TypeConstraint,
    semgrepRuleTrace: SemgrepRuleLoadStepTrace,
): MetaVarConstraintFormula<String>? = when (typeName) {
    TypeConstraint.Any -> null
    is TypeConstraint.MetaVar -> goMetaVarTypeMatcher(typeName.metaVar, semgrepRuleTrace)
    is TypeConstraint.Concrete -> when (val t = typeName.type) {
        is GoConcreteType -> MetaVarConstraintFormula.Constraint(t.toString())
        else -> MetaVarConstraintFormula.Constraint(t.toString())
    }
}

private fun GoTaintRuleGenerationCtx.goMetaVarTypeMatcher(
    metaVar: String,
    semgrepRuleTrace: SemgrepRuleLoadStepTrace,
): MetaVarConstraintFormula<String>? {
    val constraints = metaVarInfo.constraints[metaVar]
    val constraint = when (constraints) {
        null -> null
        is MetaVarConstraintOrPlaceHolder.Constraint -> constraints.constraint.constraint
        is MetaVarConstraintOrPlaceHolder.PlaceHolder -> {
            semgrepRuleTrace.error(PlaceholderTypeName())
            constraints.constraint?.constraint
        }
    }

    if (constraint == null) return null

    return constraint.transform { value ->
        when (value) {
            is MetaVarConstraint.Concrete -> value.value
            is MetaVarConstraint.RegExp -> value.regex
        }
    }
}
