package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet

/**
 * A mark-only residual condition (spec §4.1): the abstraction of a rule's
 * residual condition, with access-path bases erased and negated literals
 * dropped to `True` (E5). This is the tree form the mark-set scan evaluates
 * directly; it never expands to DNF.
 */
sealed interface MarkCond {
    data object True : MarkCond
    data object False : MarkCond

    /** `mark`: dense mark id. `literal`: dense id of the (position·access, mark, kind) literal,
     *  used only to count distinct literals of a cube (joined-ness, spec §4.1). */
    data class Lit(val mark: Int, val literal: Int) : MarkCond
    data class And(val args: List<MarkCond>) : MarkCond
    data class Or(val args: List<MarkCond>) : MarkCond
}

/**
 * One-pass evaluation of a [MarkCond] tree against a mark set, without DNF
 * expansion. These fields are exact with respect to the tree's DNF
 * (`MarkCond.toDnf` in the test oracle; `Cond.sat_toDnf` in the Lean model).
 *
 * @property sat some cube of the DNF is contained in the mark set.
 * @property hasEmpty the constant-true cube ([]) is satisfied.
 * @property singles literal ids `L` such that the cube `{L}` is satisfied.
 * @property big some cube with >= 2 distinct literals is contained in the mark set.
 */
class CondEval(val sat: Boolean, val hasEmpty: Boolean, val singles: Set<Int>, val big: Boolean) {
    /** A cube with <= 1 literal is satisfied (per-root test). */
    val smallSat: Boolean get() = hasEmpty || singles.isNotEmpty()
}

private val TRUE_EVAL = CondEval(sat = true, hasEmpty = true, singles = emptySet(), big = false)
private val FALSE_EVAL = CondEval(sat = false, hasEmpty = false, singles = emptySet(), big = false)

private fun combineOr(a: CondEval, b: CondEval): CondEval = CondEval(
    sat = a.sat || b.sat,
    hasEmpty = a.hasEmpty || b.hasEmpty,
    singles = a.singles + b.singles,
    big = a.big || b.big,
)

private fun combineAnd(a: CondEval, b: CondEval): CondEval {
    val singles = buildSet {
        if (a.hasEmpty) addAll(b.singles)
        if (b.hasEmpty) addAll(a.singles)
        addAll(a.singles.intersect(b.singles))
    }
    val big = (a.big && b.sat) ||
        (b.big && a.sat) ||
        a.singles.any { la -> b.singles.any { lb -> la != lb } }
    return CondEval(
        sat = a.sat && b.sat,
        hasEmpty = a.hasEmpty && b.hasEmpty,
        singles = singles,
        big = big,
    )
}

/** N-ary `And`/`Or` fold left, starting from `True`/`False`. */
fun MarkCond.eval(marks: BitSet): CondEval = when (this) {
    MarkCond.True -> TRUE_EVAL
    MarkCond.False -> FALSE_EVAL
    is MarkCond.Lit -> if (marks.get(mark)) {
        CondEval(sat = true, hasEmpty = false, singles = setOf(literal), big = false)
    } else {
        FALSE_EVAL
    }
    is MarkCond.And -> args.fold(TRUE_EVAL) { acc, arg -> combineAnd(acc, arg.eval(marks)) }
    is MarkCond.Or -> args.fold(FALSE_EVAL) { acc, arg -> combineOr(acc, arg.eval(marks)) }
}

/** The set of mark ids occurring anywhere in the tree. */
fun MarkCond.atoms(out: BitSet = BitSet()): BitSet {
    when (this) {
        MarkCond.True, MarkCond.False -> Unit
        is MarkCond.Lit -> out.set(mark)
        is MarkCond.And -> args.forEach { it.atoms(out) }
        is MarkCond.Or -> args.forEach { it.atoms(out) }
    }
    return out
}

/** Static: the DNF has a cube with >= 2 distinct literals (= eval(all marks).big). */
fun MarkCond.hasJoinedCube(): Boolean = eval(atoms()).big
