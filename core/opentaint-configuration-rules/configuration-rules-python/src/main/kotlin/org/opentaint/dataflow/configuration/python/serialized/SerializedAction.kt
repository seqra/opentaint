package org.opentaint.dataflow.configuration.python.serialized

import kotlinx.serialization.Serializable

/**
 * `taint:` entry attached to entry-point and source rules. Marks the given position
 * with a taint of the given `kind`.
 *
 * `decoratedWith` / `baseClass` scope the action to functions decorated with the given
 * FQN / methods whose enclosing class extends the given base. They are structural
 * properties of the matched code site, not value-level predicates, so they live as
 * dedicated fields here rather than inside [SerializedPythonCondition].
 */
@Serializable
data class SerializedPythonTaintAssignAction(
    val kind: String,
    val decoratedWith: String? = null,
    val baseClass: String? = null,
    val pos: PythonPosition,
)

/**
 * `cleans:` entry attached to cleaner rules. Removes the given `taintKind` from
 * the value at `pos`.
 */
@Serializable
data class SerializedPythonTaintCleanAction(
    val taintKind: String? = null,
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
