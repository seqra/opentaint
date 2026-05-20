package org.opentaint.dataflow.configuration.python

import org.opentaint.ir.api.python.PIRFunction

/**
 * The resolved target a compiled [TaintConfigurationItem] fires on.
 *
 * Distinct from the serialized
 * [org.opentaint.dataflow.configuration.python.serialized.PythonTarget],
 * which is name-only — name matching, signature checking and scope
 * filtering all happen inside the resolver, and the compiled rule
 * carries the already-resolved [PIRFunction] / attribute name.
 */
sealed interface Target {
    /** A function or method call site, resolved to a concrete [PIRFunction]. */
    data class Function(val method: PIRFunction) : Target

    /** A module / class attribute access by fully-qualified name. */
    data class Attribute(val name: String) : Target
}
