package org.opentaint.dataflow.configuration.python

/**
 * In-memory position model used by the [PythonTaintConfigurationItem] rules.
 *
 * Mirrors the JVM `Position` shape (`configuration-rules-jvm/.../Position.kt`):
 * leaf positions implement [Position] directly, and [PositionWithAccess] nests
 * a base [Position] under a single [PositionAccessor] — so access paths are
 * encoded as a right-leaning chain (`PositionWithAccess(PositionWithAccess(...), ...)`)
 * rather than a flat modifier list.
 *
 * Distinct from the serialized
 * [org.opentaint.dataflow.configuration.python.serialized.PythonPositionBase]:
 * the serialized form encodes `arg(*)` as `Argument(idx = null)`, which is
 * split out here into [AnyArgument] so callers can rely on [Argument.index]
 * being a concrete index.
 */
sealed interface Position

/** `arg(N)` — a specific positional argument. */
data class Argument(val index: Int) : Position

/**
 * `arg(*)` — every positional argument. Ordinary (call-site) rules carry this
 * un-expanded; the call-site rewriter unpacks it against the concrete call's
 * positional arguments, and only for `ContainsMark`. Entry-point rules expand
 * it eagerly against the signature.
 */
data object AnyArgument : Position

/** `kwarg(name)` — a keyword argument by name. */
data class KwArgument(val name: String) : Position

/** `this` — the implicit receiver of a method call. */
data object This : Position

/** `result` — the return value of a call or the value of an attribute access. */
data object Result : Position

/** `class(fqn)` — a value reachable via a fully-qualified class/attribute path. */
data class ClassRef(val fqn: String) : Position

/** A composite position: [base] further refined by a single [access] step. */
data class PositionWithAccess(
    val base: Position,
    val access: PositionAccessor,
) : Position

sealed interface PositionAccessor {
    /** `[*]` — any element of the value at the position. */
    data object ElementAccessor : PositionAccessor

    /** `.name` — the named field/attribute of the value at the position. */
    data class FieldAccessor(val name: String) : PositionAccessor
}
