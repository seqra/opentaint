package org.opentaint.dataflow.configuration.python

/**
 * What an in-memory rule fires on. Mirrors the serialized
 * [org.opentaint.dataflow.configuration.python.serialized.PythonTarget] but
 * without the serialized form's `signature:` — that gets lifted into the
 * rule's [Condition] as [Condition.SignatureMatches].
 */
sealed interface Target {
    /** `function: <fqn-or-regex>` — [name] is either an FQN or a Python-style regex pattern. */
    data class Function(val name: String) : Target

    /** `attribute: <fqn>`. */
    data class Attribute(val name: String) : Target
}
