package org.opentaint.dataflow.configuration.go.serialized

sealed interface GoNameMatcher {
    fun matches(qualifiedName: String): Boolean

    data class Simple(val name: String) : GoNameMatcher {
        override fun matches(qualifiedName: String): Boolean = name == qualifiedName
    }

    data class Pattern(val regex: String) : GoNameMatcher {
        private val compiled by lazy(LazyThreadSafetyMode.PUBLICATION) { Regex(regex) }
        override fun matches(qualifiedName: String): Boolean = compiled.matches(qualifiedName)
    }
}
