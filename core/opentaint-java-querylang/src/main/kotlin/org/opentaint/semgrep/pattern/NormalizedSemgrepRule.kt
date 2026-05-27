package org.opentaint.semgrep.pattern

import kotlinx.serialization.Serializable
import org.opentaint.semgrep.pattern.conversion.SemgrepPatternActionList

data class RuleWithMetaVars<R, C>(val rule: R, val metaVarInfo: C) {
    fun <T> map(body: (R) -> T) = RuleWithMetaVars(body(rule), metaVarInfo)
    fun <T> flatMap(body: (R) -> List<T>) = body(rule).map { RuleWithMetaVars(it, metaVarInfo) }
}

data class RawSemgrepRule(
    val patterns: List<String>,
    val patternNots: List<String>,
    val patternInsides: List<String>,
    val patternNotInsides: List<String>,
)

sealed interface RawMetaVarConstraint {
    data class RegExp(val regex: String) : RawMetaVarConstraint
    data class Pattern(val value: String) : RawMetaVarConstraint
}

data class RawMetaVarInfo(
    val focusMetaVars: Set<String>,
    val metaVariableConstraints: Map<String, MetaVarConstraintFormula<RawMetaVarConstraint>>,
)

@Serializable
sealed interface MetaVarConstraint {
    @Serializable
    data class RegExp(val regex: String) : MetaVarConstraint

    @Serializable
    data class Concrete(val value: String) : MetaVarConstraint
}

@Serializable
data class MetaVarConstraints(
    val constraint: MetaVarConstraintFormula<MetaVarConstraint>
)

@Serializable
data class ResolvedMetaVarInfo(
    val focusMetaVars: Set<String>,
    val metaVarConstraints: Map<String, MetaVarConstraints>
)

data class NormalizedSemgrepRule<P>(
    val patterns: List<P>,
    val patternNots: List<P>,
    val patternInsides: List<P>,
    val patternNotInsides: List<P>,
)

inline fun <P> NormalizedSemgrepRule<P>.map(
    body: (P) -> P
): NormalizedSemgrepRule<P> = NormalizedSemgrepRule(
    patterns.map(body),
    patternNots.map(body),
    patternInsides.map(body),
    patternNotInsides.map(body),
)

data class ActionListSemgrepRule(
    val patterns: List<SemgrepPatternActionList>,
    val patternNots: List<SemgrepPatternActionList>,
    val patternInsides: List<SemgrepPatternActionList>,
    val patternNotInsides: List<SemgrepPatternActionList>,
) {
    fun modify(
        patterns: List<SemgrepPatternActionList>? = null,
        patternNots: List<SemgrepPatternActionList>? = null,
        patternInsides: List<SemgrepPatternActionList>? = null,
        patternNotInsides: List<SemgrepPatternActionList>? = null,
    ) = ActionListSemgrepRule(
        patterns = patterns ?: this.patterns,
        patternNots = patternNots ?: this.patternNots,
        patternInsides = patternInsides ?: this.patternInsides,
        patternNotInsides = patternNotInsides ?: this.patternNotInsides,
    )
}
