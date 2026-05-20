package org.opentaint.dataflow.configuration.python.serialized

/**
 * The named entity a rule applies to. YAML rules carry either a `function:` key
 * (a callable, optionally constrained by `signature:`) or an `attribute:` key
 * (a module/class attribute access). The originating form is preserved here so
 * downstream code can distinguish calls from attribute reads.
 *
 * Not directly `@Serializable` — each rule's deserializer pulls the relevant flat
 * keys out of the YAML map and constructs the appropriate variant.
 */
sealed interface PythonTarget {
    /**
     * `function: <fqn-or-regex>` plus optional `signature: <matcher>`.
     *
     * `name` may be a fully-qualified name (`os.getenv`), a short unqualified name
     * (`dispatch_request`), or a regex pattern (`.*`).
     */
    data class Function(
        val function: String,
        val signature: SerializedPythonSignatureMatcher? = null,
    ) : PythonTarget

    /** `attribute: <fqn>` — taint flows from / to reading this attribute. */
    data class Attribute(
        val attribute: String,
    ) : PythonTarget
}
