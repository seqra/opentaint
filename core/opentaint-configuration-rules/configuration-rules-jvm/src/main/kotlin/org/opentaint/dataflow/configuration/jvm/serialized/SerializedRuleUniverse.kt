package org.opentaint.dataflow.configuration.jvm.serialized

import java.util.concurrent.ConcurrentHashMap

/**
 * Everything the loaded rule sets can ever put into an access path: taint kinds, artificial
 * class-static positions, and the concrete class names their matchers reference.
 *
 * Serialized rule objects are constructed while rules load, before any analysis thread runs,
 * so by analysis start these sets are complete. The analyzer pre-interns them in canonical
 * order; without that, the accessor indices for rule-derived marks and statics are assigned
 * in analysis-thread arrival order, which leaks through iteration order into edge identities
 * and makes trace fingerprints differ between runs over identical input.
 */
object SerializedRuleUniverse {
    private val taintKinds = ConcurrentHashMap.newKeySet<String>()
    private val staticPositionClassNames = ConcurrentHashMap.newKeySet<String>()
    private val matcherClassNames = ConcurrentHashMap.newKeySet<String>()
    private val fieldModifiers = ConcurrentHashMap.newKeySet<Triple<String, String, String>>()

    fun recordTaintKind(kind: String?) {
        kind?.let(taintKinds::add)
    }

    fun recordStaticPosition(className: String) {
        staticPositionClassNames.add(className)
    }

    fun recordMatcherClass(packageName: String, className: String) {
        if (className.isEmpty()) return
        matcherClassNames.add(if (packageName.isEmpty()) className else "$packageName.$className")
    }

    fun recordFieldModifier(className: String, fieldName: String, fieldType: String) {
        fieldModifiers.add(Triple(className, fieldName, fieldType))
    }

    /** Field accessors the rules reference directly, including virtual fields that no class declares. */
    fun fieldModifiers(): Set<Triple<String, String, String>> = fieldModifiers

    fun taintKinds(): Set<String> = taintKinds
    fun staticPositionClassNames(): Set<String> = staticPositionClassNames
    fun matcherClassNames(): Set<String> = matcherClassNames
}
