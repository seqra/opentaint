package org.opentaint.semgrep.go.pattern.conversion.go

import org.opentaint.semgrep.go.pattern.conversion.GoLanguageStrategy.Companion.FIELD_AUX_MODIFIER
import org.opentaint.semgrep.pattern.conversion.ParamCondition
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternAction.SignatureModifierValue

fun ParamCondition.ParamModifier.dropFieldResultModifier(
    handleFieldModifier: (String) -> Unit
): ParamCondition.ParamModifier? {
    val value = this.modifier.value as? SignatureModifierValue.StringValue ?: return this
    if (value.paramName != FIELD_AUX_MODIFIER) return this
    handleFieldModifier(value.value)
    return null
}
