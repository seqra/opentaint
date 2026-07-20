package org.opentaint.semgrep.pattern.conversion.automata

import org.opentaint.semgrep.pattern.conversion.automata.MethodFormula.And
import org.opentaint.semgrep.pattern.conversion.automata.MethodFormula.False
import org.opentaint.semgrep.pattern.conversion.automata.MethodFormula.Or
import org.opentaint.semgrep.pattern.conversion.automata.MethodFormula.True

/**
 * A positive whole-object taint occurrence `$*X` (star = true) that coincides, at the SAME
 * parameter position, with an unstarred `pattern-not $X` (star = false) — the T/F cell of the
 * star/pattern-not coincidence matrix. The "keep field, drop base" scoped semantics this would
 * imply is NOT implemented; the combination is treated as a full (exclude-all) match, same as the
 * already-correct T/T case. Collected here during formula simplification so the nearest layer that
 * owns a [org.opentaint.semgrep.pattern.SemgrepLoadTrace] can surface a non-fatal diagnostic.
 */
data class StarPatternNotCoincidence(val metavar: String)

class MethodFormulaManager(initialPredicates: List<Predicate> = emptyList()) {
    /** Accumulates T/F star/pattern-not coincidences found while simplifying this rule's formulas. */
    val starPatternNotCoincidences: MutableSet<StarPatternNotCoincidence> = linkedSetOf()

    private val predicateIds = hashMapOf<Predicate, Int>().also {
        initialPredicates.forEachIndexed { index, predicate ->
            it[predicate] = index
        }
    }

    private val predicates = arrayListOf<Predicate>().also { it.addAll(initialPredicates) }

    val allPredicateIds: List<PredicateId>
        get() = (1..predicates.size).toList()

    val allPredicates: List<Predicate>
        get() = predicates.toList()

    fun predicateId(predicate: Predicate): PredicateId = predicateIds.getOrPut(predicate) {
        val id = predicates.size
        predicates.add(predicate)
        id + 1
    }

    fun predicate(predicateId: PredicateId): Predicate {
        return predicates[predicateId - 1]
    }

    fun mkCube(cube: MethodFormulaCubeCompact): MethodFormula {
        if (cube.isEmpty) return True
        return MethodFormula.Cube(cube, negated = false)
    }

    fun mkAnd(all: List<MethodFormula>): MethodFormula = when (all.size) {
        0 -> True
        1 -> all.single()
        else -> And(all.toTypedArray())
    }

    fun mkOr(any: List<MethodFormula>): MethodFormula = when (any.size) {
        0 -> False
        1 -> any.single()
        else -> Or(any.toTypedArray())
    }
}
