package org.opentaint.dataflow.configuration.python.serialized

import kotlinx.serialization.Serializable

/**
 * `taint:` entry attached to entry-point and source rules. Marks the given position
 * with a taint of the given `kind`.
 *
 * Decorator / base-class scoping is a predicate on the matched function, not a property
 * of the action, so it lives in the rule's [SerializedPythonCondition]
 * ([SerializedPythonCondition.MethodDecorated] / [SerializedPythonCondition.ClassExtends]),
 * where it composes with `not` / `anyOf` and applies to every rule kind — not just those
 * that carry `taint:` actions.
 */
@Serializable
data class SerializedPythonTaintAssignAction(
    val kind: String,
    val pos: PythonPosition,
)

/**
 * `cleans:` entry attached to cleaner rules. Removes the given `taintKind` from
 * the value at `pos`.
 */
@Serializable
data class SerializedPythonTaintCleanAction(
    val taintKind: String,
    val pos: PythonPosition,
)

/**
 * `copy:` entry attached to passThrough rules. Propagates taint from `from` to `to`,
 * regardless of kind.
 */
@Serializable
data class SerializedPythonTaintPassAction(
    val taintKind: String? = null,
    val from: PythonPosition,
    val to: PythonPosition,
)
