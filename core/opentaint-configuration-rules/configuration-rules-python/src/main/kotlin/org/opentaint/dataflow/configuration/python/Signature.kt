package org.opentaint.dataflow.configuration.python

/**
 * Compiled form of the serialized
 * [org.opentaint.dataflow.configuration.python.serialized.SerializedPythonSignatureMatcher]
 * string. The serialized side encodes signatures as a single string like
 * `(str, int) *`; the in-memory form keeps argument types and the return type
 * as a structured list of [TypeMatcher]s.
 */
data class Signature(
    val args: List<TypeMatcher>,
    val returnType: TypeMatcher,
)

sealed interface TypeMatcher {
    /** `*` — matches any type. */
    data object AnyType : TypeMatcher

    /** Exact type-name match. */
    data class Exact(val name: String) : TypeMatcher
}
