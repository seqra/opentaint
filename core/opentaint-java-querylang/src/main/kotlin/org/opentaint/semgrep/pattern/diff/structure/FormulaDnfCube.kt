package org.opentaint.semgrep.pattern.diff.structure

import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.MetaVarConstraintFormula
import org.opentaint.semgrep.pattern.RawMetaVarConstraint
import org.opentaint.semgrep.pattern.RawMetaVarInfo
import org.opentaint.semgrep.pattern.RawSemgrepRule
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace
import org.opentaint.semgrep.pattern.formulaToRawDnfCubes

data class FormulaDnfCube(
    val ordinal: Int,
    val formula: Formula,
    val raw: RuleWithMetaVars<RawSemgrepRule, RawMetaVarInfo>,
    val key: CanonicalCubeKey,
)

/**
 * A deterministic, order-independent identity for one DNF conjunction.
 *
 * User metavariable names are deliberately retained verbatim.
 */
data class CanonicalCubeKey(
    val patterns: List<String>,
    val patternNots: List<String>,
    val patternInsides: List<String>,
    val patternNotInsides: List<String>,
    val focusMetaVars: List<String>,
    val metaVariableConstraints: List<CanonicalMetaVariableConstraint>,
)

data class CanonicalMetaVariableConstraint(
    val metaVariable: String,
    val formula: CanonicalConstraintFormula,
)

sealed interface CanonicalConstraintFormula {
    data class Literal(
        val negated: Boolean,
        val kind: ConstraintKind,
        val value: String,
    ) : CanonicalConstraintFormula

    data class And(val children: List<CanonicalConstraintFormula>) : CanonicalConstraintFormula
    data class Or(val children: List<CanonicalConstraintFormula>) : CanonicalConstraintFormula
}

enum class ConstraintKind { PATTERN, REGEX }

/**
 * Splits [formula] with the same NNF/DNF conversion used by normal raw conversion. Invalid cubes are
 * omitted in exactly the same way as that conversion and diagnostics are written to [trace].
 */
fun formulaToDnfCubes(
    formula: Formula,
    trace: SemgrepRuleLoadStepTrace,
): List<FormulaDnfCube> {
    return formulaToRawDnfCubes(formula, trace).map { cube ->
        FormulaDnfCube(
            ordinal = cube.ordinal,
            formula = cube.formula,
            raw = cube.raw,
            key = cube.raw.toCanonicalCubeKey(),
        )
    }
}

private fun RuleWithMetaVars<RawSemgrepRule, RawMetaVarInfo>.toCanonicalCubeKey(): CanonicalCubeKey =
    CanonicalCubeKey(
        patterns = rule.patterns.sorted(),
        patternNots = rule.patternNots.sorted(),
        patternInsides = rule.patternInsides.sorted(),
        patternNotInsides = rule.patternNotInsides.sorted(),
        focusMetaVars = metaVarInfo.focusMetaVars.sorted(),
        metaVariableConstraints = metaVarInfo.metaVariableConstraints.entries
            .map { (name, formula) -> CanonicalMetaVariableConstraint(name, formula.canonical()) }
            .sortedWith(compareBy({ it.metaVariable }, { it.formula.stableKey() })),
    )

private fun MetaVarConstraintFormula<RawMetaVarConstraint>.canonical(): CanonicalConstraintFormula = when (this) {
    is MetaVarConstraintFormula.Constraint -> constraint.canonicalLiteral(negated = false)
    is MetaVarConstraintFormula.NegatedConstraint -> constraint.canonicalLiteral(negated = true)
    is MetaVarConstraintFormula.And -> CanonicalConstraintFormula.And(
        args.map { it.canonical() }.sortedBy { it.stableKey() }
    )
    is MetaVarConstraintFormula.Or -> CanonicalConstraintFormula.Or(
        args.map { it.canonical() }.sortedBy { it.stableKey() }
    )
}

private fun RawMetaVarConstraint.canonicalLiteral(negated: Boolean): CanonicalConstraintFormula.Literal =
    when (this) {
        is RawMetaVarConstraint.Pattern -> CanonicalConstraintFormula.Literal(
            negated, ConstraintKind.PATTERN, value
        )
        is RawMetaVarConstraint.RegExp -> CanonicalConstraintFormula.Literal(
            negated, ConstraintKind.REGEX, regex
        )
    }

private fun CanonicalConstraintFormula.stableKey(): String = when (this) {
    is CanonicalConstraintFormula.Literal ->
        "L:${if (negated) 1 else 0}:${kind.name}:${value.length}:$value"
    is CanonicalConstraintFormula.And -> "A:${children.joinToString(separator = "", transform = { it.stableKey() })}"
    is CanonicalConstraintFormula.Or -> "O:${children.joinToString(separator = "", transform = { it.stableKey() })}"
}
