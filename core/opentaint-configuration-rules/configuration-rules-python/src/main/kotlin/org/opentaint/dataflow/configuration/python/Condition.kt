package org.opentaint.dataflow.configuration.python

/**
 * In-memory condition AST attached to every [PythonTaintConfigurationItem].
 * Distinct from the serialized
 * [org.opentaint.dataflow.configuration.python.serialized.SerializedPythonCondition]
 * because (a) [ContainsMark] uses the local [Position] / [TaintMark] types and
 * (b) it has dedicated variants for the structural scopes ([DecoratedWith],
 * [BaseClass]) that the serialized model expresses as per-action fields.
 *
 * [ConstantTrue] is the "no condition" baseline — `condition` on items is
 * non-nullable so callers don't have to special-case null.
 */
sealed interface Condition {

    data object ConstantTrue : Condition

    data class Not(val arg: Condition) : Condition

    data class And(val args: List<Condition>) : Condition

    data class Or(val args: List<Condition>) : Condition

    /** `tainted: <mark>` at [pos]. */
    data class ContainsMark(val mark: TaintMark, val pos: Position) : Condition

    /** Function/method scope: the matched site is decorated with [fqn]. */
    data class DecoratedWith(val fqn: String) : Condition

    /** Method scope: the matched method's enclosing class extends [fqn]. */
    data class BaseClass(val fqn: String) : Condition

    /** Function-target scope: the matched function's signature satisfies [signature]. */
    data class SignatureMatches(val signature: Signature) : Condition
}
