package org.opentaint.dataflow.configuration.python

/**
 * Boolean predicate evaluated against the dataflow state at a matched
 * call / attribute site. [ConstantTrue] is the "no condition"
 * baseline; rule `condition` fields are non-nullable so callers don't
 * special-case null.
 */
sealed interface Condition {

    data object ConstantTrue : Condition

    data class Not(val arg: Condition) : Condition

    data class And(val args: List<Condition>) : Condition

    data class Or(val args: List<Condition>) : Condition

    /** `tainted: <mark>` at [pos]. */
    data class ContainsMark(val mark: TaintMark, val pos: Position) : Condition
}
