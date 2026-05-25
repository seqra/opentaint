package org.opentaint.dataflow.go.rules.serialized

/**
 * Matches a Go function by qualified name (e.g. "util.Source").
 *
 * Go function names in our IR are flat qualified strings — package-or-receiver plus name —
 * so there is no need for the JVM-style package/class/name triple. A pattern matcher is
 * provided so the upstream automata conversion can encode metavariable-based name patterns.
 */
sealed interface GoFunctionMatcher {
    fun matches(qualifiedName: String): Boolean

    data class Simple(val name: String) : GoFunctionMatcher {
        override fun matches(qualifiedName: String): Boolean = name == qualifiedName
    }

    data class Pattern(val regex: String) : GoFunctionMatcher {
        private val compiled by lazy(LazyThreadSafetyMode.PUBLICATION) { Regex(regex) }
        override fun matches(qualifiedName: String): Boolean = compiled.matches(qualifiedName)
    }
}
